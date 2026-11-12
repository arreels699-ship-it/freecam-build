/*
 * libfreecam.so  -  /fc freecam for Minecraft PE 1.2.3 (32-bit ARM, armeabi-v7a)
 *
 *   /fc            toggle freecam
 *   /fc on | off
 *   /fc speed 5    speed multiplier, 1..30 (1 = normal flying pace, default 4)
 *   (also /freecam ..., and the same with a leading "." instead of "/")
 *
 * HOW IT WORKS (all hook points were checked against the 1.2.3 libminecraftpe.so
 * you sent; none of them are functions that libSaturn.so hooks):
 *
 *   1. LocalPlayer::move(Vec3 const&)  - virtual, patched in LocalPlayer's vtable.
 *      While freecam is on the game's own movement/collision is skipped and the
 *      player is moved straight through blocks with Entity::setPos (noclip).
 *   2. BatchedPacketSender::send(...)  - virtual, patched in its vtable.
 *      While freecam is on, MovePlayerPacket is dropped so the server never sees
 *      you move. A TextPacket whose text is "/fc ..." is swallowed (not sent to
 *      chat) and turned into a command.
 *   3. On "off" you are put back exactly where you were when you turned it on.
 *
 * SAFETY: nothing is patched unless the vtable slot currently holds exactly the
 * address that dlsym() returns for the expected function. If the game is a
 * different build the library does nothing instead of crashing.
 *
 * LIMITS (be aware):
 *   - Vertical movement only works while you are flying (double-tap jump in
 *     creative). Not flying = horizontal noclip only.
 *   - Your body is NOT left standing at the start spot; the camera is your player.
 *   - Use creative mode: suffocation/mob damage is not blocked.
 *   - Using it on multiplayer servers can get you banned.
 *
 * Fallback trigger if chat interception does not work on your build: create a
 * text file /sdcard/games/com.mojang/fc_cmd.txt containing e.g.  /fc  or
 * /fc speed 8   (it is read and deleted within half a second).
 *
 * Plain C on purpose (no libstdc++), so it cannot clash with the game's STL.
 */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <fcntl.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#define DEFAULT_SPEED 4.0f
#define MAX_SPEED     30.0f
#define CMD_FILE      "/sdcard/games/com.mojang/fc_cmd.txt"
#define LP_VTABLE_SIZE 1076   /* size of _ZTV11LocalPlayer in 1.2.3 */

typedef struct { float x, y, z; } Vec3;

/* ------------------------------------------------------------------ logging */
typedef int (*logprint_t)(int, const char *, const char *, ...);
static logprint_t g_logp;
#define LOG(...) do { if (g_logp) g_logp(4, "FreeCam", __VA_ARGS__); } while (0)

/* ------------------------------------------------------------------- state */
static volatile int g_fc;            /* freecam active                        */
static float        g_speed = DEFAULT_SPEED;
static Vec3         g_anchor;        /* where you were when it was switched on */
static void        *g_owner;         /* the LocalPlayer that is frozen         */
static char         g_pending[96];   /* command queued from another thread     */
static volatile int g_has_pending;

/* ------------------------------------------------ game functions (dlsym'd) */
static void         (*LP_move_orig)(void *, const Vec3 *);
static const Vec3  *(*Entity_getPos)(const void *);
static void         (*Entity_setPos)(void *, const Vec3 *);
static unsigned int (*LP_isFlying)(const void *);
static void         (*LP_display)(void *, const void *, const void *);
static void         (*BPS_send1_orig)(void *, const void *);
static void         (*BPS_send2_orig)(void *, const void *, const void *);
static const char  *g_move_vptr;     /* vptr value of a MovePlayerPacket */
static const char  *g_text_vptr;     /* vptr value of a TextPacket       */

/* --------------------------------------------------------- command parsing */
typedef enum { CMD_NONE = 0, CMD_TOGGLE, CMD_ON, CMD_OFF, CMD_SPEED, CMD_SPEED_BAD } cmd_t;

static cmd_t parse_command(const char *s, float *speed_out)
{
    char buf[96];
    size_t i, n = 0;
    char *tok[4];
    int nt = 0;

    while (*s == ' ' || *s == '\t') s++;
    if (*s != '/' && *s != '.') return CMD_NONE;
    s++;
    for (i = 0; s[i] && n < sizeof buf - 1; i++) {
        char c = s[i];
        if (c >= 'A' && c <= 'Z') c = (char)(c + 32);
        buf[n++] = c;
    }
    buf[n] = 0;

    for (i = 0; i < n && nt < 4;) {
        while (i < n && (buf[i] == ' ' || buf[i] == '\t')) buf[i++] = 0;
        if (i >= n) break;
        tok[nt++] = &buf[i];
        while (i < n && buf[i] != ' ' && buf[i] != '\t') i++;
    }
    if (nt == 0) return CMD_NONE;
    if (strcmp(tok[0], "fc") != 0 && strcmp(tok[0], "freecam") != 0) return CMD_NONE;
    if (nt == 1) return CMD_TOGGLE;
    if (strcmp(tok[1], "on") == 0)  return CMD_ON;
    if (strcmp(tok[1], "off") == 0) return CMD_OFF;
    if (strcmp(tok[1], "speed") == 0 || strcmp(tok[1], "s") == 0) {
        char *end;
        float v;
        if (nt < 3) return CMD_SPEED_BAD;
        v = strtof(tok[2], &end);
        if (end == tok[2] || *end != 0 || !(v == v)) return CMD_SPEED_BAD;
        if (v < 1.0f) v = 1.0f;
        if (v > MAX_SPEED) v = MAX_SPEED;
        if (speed_out) *speed_out = v;
        return CMD_SPEED;
    }
    return CMD_TOGGLE;
}

/* ------------------------------------------------- safe memory reads (pipe) */
static int g_pipe[2] = { -1, -1 };

static int safe_read(const void *addr, void *out, size_t n)
{
    ssize_t r;
    char drain[128];
    if (g_pipe[0] < 0 || n == 0 || n > sizeof drain) return 0;
    r = write(g_pipe[1], addr, n);          /* EFAULT instead of a crash */
    if (r != (ssize_t)n) {
        while (read(g_pipe[0], drain, sizeof drain) > 0) { }
        return 0;
    }
    return read(g_pipe[0], out, n) == (ssize_t)n;
}

static int safe_read_cstr(const void *addr, char *out, size_t cap)
{
    static const size_t tries[] = { 64, 32, 16, 8, 4 };
    size_t t;
    for (t = 0; t < sizeof tries / sizeof tries[0]; t++) {
        size_t n = tries[t] < cap - 1 ? tries[t] : cap - 1;
        if (safe_read(addr, out, n)) { out[n] = 0; return 1; }
    }
    return 0;
}

/*
 * A chat packet holds the message as a std::string. With the game's old
 * (copy-on-write) std::string that is just a pointer to the characters, so we
 * look at every word of the packet and check whether it points at "/fc...".
 */
static int packet_command(const void *pkt, char *out, size_t outsz)
{
    size_t off;
    for (off = 4; off <= 0x48; off += 4) {
        uint32_t w;
        char head[8], full[96];
        if (!safe_read((const char *)pkt + off, &w, 4)) break;
        if (w < 0x10000u) continue;
        if (!safe_read((const void *)(uintptr_t)w, head, 3)) continue;
        if ((head[0] != '/' && head[0] != '.') ||
            (head[1] != 'f' && head[1] != 'F')) continue;
        if (!safe_read_cstr((const void *)(uintptr_t)w, full, sizeof full)) continue;
        if (parse_command(full, NULL) != CMD_NONE) {
            strncpy(out, full, outsz - 1);
            out[outsz - 1] = 0;
            return 1;
        }
    }
    return 0;
}

/* ----------------------------------------------------- in-game text output */
static void say(void *self, const char *text)
{
    LOG("%s", text);
#ifdef __arm__
    if (self && LP_display) {
        struct rep { unsigned len, cap; int refc; } *r;
        size_t n = strlen(text);
        char *d, *strobj;
        unsigned vec[3] = { 0, 0, 0 };
        r = (struct rep *)malloc(sizeof *r + n + 1);
        if (!r) return;
        r->len = (unsigned)n; r->cap = (unsigned)n; r->refc = 0x40000000; /* never freed */
        d = (char *)(r + 1);
        memcpy(d, text, n + 1);
        strobj = d;                       /* COW std::string == pointer to chars */
        LP_display(self, &strobj, vec);   /* LocalPlayer::displayLocalizableMessage */
    }
#else
    (void)self;
#endif
}

/* ------------------------------------------------------------ freecam logic */
static void fc_enable(void *self)
{
    char msg[96];
    if (g_fc) { say(self, "\xc2\xa7" "eFreecam is already on"); return; }
    g_anchor = *Entity_getPos(self);
    g_owner = self;
    g_fc = 1;
    snprintf(msg, sizeof msg, "\xc2\xa7" "aFreecam ON\xc2\xa7r  speed %.1f%s", g_speed,
             (LP_isFlying && (LP_isFlying(self) & 0xff)) ? "" : "  (double-tap jump to fly)");
    say(self, msg);
}

static void fc_disable(void *self)
{
    if (!g_fc) { say(self, "\xc2\xa7" "eFreecam is already off"); return; }
    g_fc = 0;
    Entity_setPos(self, &g_anchor);
    say(self, "\xc2\xa7" "cFreecam OFF\xc2\xa7r");
}

static void process_pending(void *self)
{
    char cmd[96];
    float sp = g_speed;
    cmd_t c;
    if (!g_has_pending) return;
    memcpy(cmd, g_pending, sizeof cmd);
    cmd[sizeof cmd - 1] = 0;
    __sync_synchronize();
    g_has_pending = 0;

    c = parse_command(cmd, &sp);
    switch (c) {
    case CMD_TOGGLE:    if (g_fc) fc_disable(self); else fc_enable(self); break;
    case CMD_ON:        fc_enable(self);  break;
    case CMD_OFF:       fc_disable(self); break;
    case CMD_SPEED: {
        char msg[64];
        g_speed = sp;
        snprintf(msg, sizeof msg, "Freecam speed: %.1f", g_speed);
        say(self, msg);
        break;
    }
    case CMD_SPEED_BAD: say(self, "Usage: /fc speed 1-30"); break;
    default: break;
    }
}

static void queue_command(const char *cmd)
{
    strncpy(g_pending, cmd, sizeof g_pending - 1);
    g_pending[sizeof g_pending - 1] = 0;
    __sync_synchronize();
    g_has_pending = 1;
}

/* ---------------------------------------------------------------- the hooks */
static void LP_move_hook(void *self, const Vec3 *d)
{
    Vec3 p, n;
    float sp, dy;

    process_pending(self);

    if (!g_fc) { LP_move_orig(self, d); return; }
    if (self != g_owner) {               /* new world / new player object */
        g_fc = 0;
        LP_move_orig(self, d);
        return;
    }

    p  = *Entity_getPos(self);
    sp = g_speed;
    dy = (LP_isFlying && (LP_isFlying(self) & 0xff)) ? d->y : 0.0f;
    n.x = p.x + d->x * sp;
    n.y = p.y + dy * sp;
    n.z = p.z + d->z * sp;
    Entity_setPos(self, &n);             /* noclip: no collision check */
}

/* returns 1 if the packet must be dropped */
static int on_packet(const void *pkt)
{
    const char *vp;
    if (!pkt) return 0;
    vp = *(const char *const *)pkt;
    if (vp == g_move_vptr) return g_fc;           /* hide movement while in freecam */
    if (vp == g_text_vptr) {
        char cmd[96];
        if (packet_command(pkt, cmd, sizeof cmd)) {
            queue_command(cmd);
            return 1;                             /* keep "/fc" out of chat */
        }
    }
    return 0;
}

static void BPS_send1_hook(void *self, const void *pkt)
{
    if (on_packet(pkt)) return;
    BPS_send1_orig(self, pkt);
}

static void BPS_send2_hook(void *self, const void *guid, const void *pkt)
{
    if (on_packet(pkt)) return;
    BPS_send2_orig(self, guid, pkt);
}

/* ------------------------------------------------------------- vtable patch */
static int prot_of(const void *addr)
{
    FILE *f = fopen("/proc/self/maps", "r");
    char line[512];
    int prot = PROT_READ;
    if (!f) return prot;
    while (fgets(line, sizeof line, f)) {
        unsigned long lo, hi;
        char perm[8];
        if (sscanf(line, "%lx-%lx %7s", &lo, &hi, perm) == 3 &&
            (unsigned long)addr >= lo && (unsigned long)addr < hi) {
            prot = 0;
            if (perm[0] == 'r') prot |= PROT_READ;
            if (perm[1] == 'w') prot |= PROT_WRITE;
            if (perm[2] == 'x') prot |= PROT_EXEC;
            break;
        }
    }
    fclose(f);
    return prot;
}

static int patch_slot(void **slot, void *expect, void *repl)
{
    long pg = sysconf(_SC_PAGESIZE);
    void *page = (void *)((uintptr_t)slot & ~(uintptr_t)(pg - 1));
    int old = prot_of(slot);
    if (*slot != expect) return 0;                       /* verify before patching */
    if (mprotect(page, (size_t)pg, PROT_READ | PROT_WRITE) != 0) return 0;
    *slot = repl;
    mprotect(page, (size_t)pg, old);
    return 1;
}

static void **find_slot(void *vtable, size_t bytes, void *target)
{
    void **v = (void **)vtable;
    size_t i;
    for (i = 0; i < bytes / sizeof(void *); i++)
        if (v[i] == target) return &v[i];
    return NULL;
}

/* ---------------------------------------------------------------- installer */
static int g_done_move, g_done_send1, g_done_send2;

static void *find_game_lib(void)
{
    FILE *f = fopen("/proc/self/maps", "r");
    char line[512];
    void *h = NULL;
    if (!f) return NULL;
    while (fgets(line, sizeof line, f)) {
        char *p = strstr(line, "/libminecraftpe");
        if (p) {
            char *e = strchr(p, '\n');
            if (e) *e = 0;
            h = dlopen(p, RTLD_NOW);        /* already mapped: returns same handle */
            if (!h) h = dlopen(p + 1, RTLD_NOW);
            if (h) break;
        }
    }
    fclose(f);
    return h;
}

/* returns 1 when everything is installed */
static int install_hooks(void *h)
{
    void *vt_lp, *vt_bps, *vt_text, *vt_move;
    void *send1, *send2;
    void **slot;

    Entity_getPos = (const Vec3 *(*)(const void *))dlsym(h, "_ZNK6Entity6getPosEv");
    Entity_setPos = (void (*)(void *, const Vec3 *))dlsym(h, "_ZN6Entity6setPosERK4Vec3");
    LP_isFlying   = (unsigned int (*)(const void *))dlsym(h, "_ZNK11LocalPlayer8isFlyingEv");
    LP_display    = (void (*)(void *, const void *, const void *))
                    dlsym(h, "_ZN11LocalPlayer25displayLocalizableMessageERKSsRKSt6vectorISsSaISsEE");
    if (!LP_move_orig)
        LP_move_orig = (void (*)(void *, const Vec3 *))dlsym(h, "_ZN11LocalPlayer4moveERK4Vec3");
    vt_lp   = dlsym(h, "_ZTV11LocalPlayer");
    vt_bps  = dlsym(h, "_ZTV19BatchedPacketSender");
    vt_text = dlsym(h, "_ZTV10TextPacket");
    vt_move = dlsym(h, "_ZTV16MovePlayerPacket");
    send1   = dlsym(h, "_ZN19BatchedPacketSender4sendERK6Packet");
    send2   = dlsym(h, "_ZN19BatchedPacketSender4sendERKN6RakNet10RakNetGUIDERK6Packet");

    if (!Entity_getPos || !Entity_setPos || !LP_move_orig || !vt_lp) {
        LOG("required game symbols not found - wrong game version?");
        return 0;
    }
    if (vt_text) g_text_vptr = (const char *)vt_text + 8;
    if (vt_move) g_move_vptr = (const char *)vt_move + 8;

    if (!g_done_move) {
        slot = find_slot(vt_lp, LP_VTABLE_SIZE, (void *)LP_move_orig);
        if (slot && patch_slot(slot, (void *)LP_move_orig, (void *)LP_move_hook)) {
            g_done_move = 1;
            LOG("hooked LocalPlayer::move");
        }
    }
    if (vt_bps && send1 && !g_done_send1) {
        BPS_send1_orig = (void (*)(void *, const void *))send1;
        if (patch_slot((void **)((char *)vt_bps + 16), send1, (void *)BPS_send1_hook)) {
            g_done_send1 = 1;
            LOG("hooked BatchedPacketSender::send(Packet)");
        }
    }
    if (vt_bps && send2 && !g_done_send2) {
        BPS_send2_orig = (void (*)(void *, const void *, const void *))send2;
        if (patch_slot((void **)((char *)vt_bps + 20), send2, (void *)BPS_send2_hook)) {
            g_done_send2 = 1;
            LOG("hooked BatchedPacketSender::send(GUID,Packet)");
        }
    }
    return g_done_move && g_done_send1 && g_done_send2;
}

static void poll_command_file(void)
{
    struct stat st;
    if (stat(CMD_FILE, &st) == 0) {
        char buf[96] = { 0 };
        FILE *f = fopen(CMD_FILE, "r");
        if (f) {
            size_t n = fread(buf, 1, sizeof buf - 1, f);
            fclose(f);
            buf[n] = 0;
            while (n > 0 && (buf[n - 1] == '\n' || buf[n - 1] == '\r' || buf[n - 1] == ' ')) buf[--n] = 0;
            if (parse_command(buf, NULL) != CMD_NONE) queue_command(buf);
        }
        unlink(CMD_FILE);
    }
}

static void *init_thread(void *arg)
{
    int i;
    (void)arg;
    g_logp = (logprint_t)dlsym(RTLD_DEFAULT, "__android_log_print");
    if (pipe(g_pipe) == 0) {
        fcntl(g_pipe[0], F_SETFL, O_NONBLOCK);
        fcntl(g_pipe[1], F_SETFL, O_NONBLOCK);
    }
    LOG("loaded, waiting for libminecraftpe.so");
    for (i = 0; i < 240; i++) {                 /* up to ~2 minutes */
        void *h = find_game_lib();
        if (h && install_hooks(h)) { LOG("all hooks installed"); break; }
        usleep(500000);
    }
    if (!g_done_move)  LOG("WARNING: move hook NOT installed - freecam will not work");
    if (!g_done_send1) LOG("WARNING: send(Packet) hook not installed - /fc chat command and position hiding unavailable");
    for (;;) { poll_command_file(); usleep(300000); }
    return NULL;
}

#ifndef FC_TEST
__attribute__((constructor)) static void fc_init(void)
{
    pthread_t t;
    if (pthread_create(&t, NULL, init_thread, NULL) == 0) pthread_detach(t);
}
#endif

/* ------------------------------------------------------ host unit tests only */
#ifdef FC_TEST
#include <assert.h>
int main(void)
{
    float sp = 0;
    assert(parse_command("/fc", &sp) == CMD_TOGGLE);
    assert(parse_command("  /FC  ", &sp) == CMD_TOGGLE);
    assert(parse_command(".fc", &sp) == CMD_TOGGLE);
    assert(parse_command("/freecam", &sp) == CMD_TOGGLE);
    assert(parse_command("/fc on", &sp) == CMD_ON);
    assert(parse_command("/fc off", &sp) == CMD_OFF);
    assert(parse_command("/fc speed 5", &sp) == CMD_SPEED && sp == 5.0f);
    assert(parse_command("/fc speed 2.5", &sp) == CMD_SPEED && sp == 2.5f);
    assert(parse_command("/fc s 99", &sp) == CMD_SPEED && sp == MAX_SPEED);
    assert(parse_command("/fc speed 0", &sp) == CMD_SPEED && sp == 1.0f);
    assert(parse_command("/fc speed", &sp) == CMD_SPEED_BAD);
    assert(parse_command("/fc speed abc", &sp) == CMD_SPEED_BAD);
    assert(parse_command("/fcx", &sp) == CMD_NONE);
    assert(parse_command("/fly", &sp) == CMD_NONE);
    assert(parse_command("hello /fc", &sp) == CMD_NONE);
    assert(parse_command("/give me stuff", &sp) == CMD_NONE);
    assert(parse_command("", &sp) == CMD_NONE);

    /* fake TextPacket: [vptr][type][author ptr][message ptr][...] on a 64-bit host
       is not layout compatible, so test the scan with 32-bit-sized words only
       when the host has 32-bit pointers; otherwise just test safe_read. */
    pipe(g_pipe);
    fcntl(g_pipe[0], F_SETFL, O_NONBLOCK);
    fcntl(g_pipe[1], F_SETFL, O_NONBLOCK);
    {
        char src[16] = "hello", dst[16];
        assert(safe_read(src, dst, 6) && strcmp(dst, "hello") == 0);
        assert(!safe_read((void *)8, dst, 4));          /* bad pointer: no crash */
        assert(safe_read(src, dst, 6));                  /* pipe still usable */
    }
    if (sizeof(void *) == 4) {
        uint32_t pkt[12] = { 0 };
        static char author[] = "Steve";
        static char msg[] = "/fc speed 7";
        char out[96];
        pkt[1] = 1; pkt[2] = (uint32_t)(uintptr_t)author; pkt[3] = (uint32_t)(uintptr_t)msg;
        assert(packet_command(pkt, out, sizeof out) && strcmp(out, "/fc speed 7") == 0);
        pkt[3] = (uint32_t)(uintptr_t)"just chatting";
        assert(!packet_command(pkt, out, sizeof out));
    }
    puts("host tests passed");
    return 0;
}
#endif
