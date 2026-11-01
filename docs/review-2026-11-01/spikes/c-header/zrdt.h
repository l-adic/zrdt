/* zrdt.h -- proposed revision of PLAN.md 3.3 (sketch; compiles with -std=c11 -Wall -Wextra -pedantic) */
#ifndef ZRDT_H
#define ZRDT_H
#include <stddef.h>
#include <stdint.h>
#ifdef __cplusplus
extern "C" {
#endif

#define ZRDT_ABI_VERSION      1u
#define ZRDT_MAX_PAYLOAD      (1u << 20)   /* bytes; enforced in Lean, ZRDT_ETOOBIG otherwise */
#define ZRDT_MAX_LINKS        1024u        /* after dedup */
#define ZRDT_MAX_ATTACHMENTS  256u

typedef struct zrdt_store zrdt_store;                            /* opaque; holds exactly one Lean reference */
typedef struct { uint8_t b[32]; } zrdt_digest;
typedef struct { uint8_t b[16]; } zrdt_aci;
typedef struct { const uint8_t *ptr; size_t len; } zrdt_bytes;   /* borrowed input */
typedef struct { uint8_t *ptr; size_t len; } zrdt_buf;           /* owned output */
typedef struct { zrdt_digest *ptr; size_t len; } zrdt_digests;   /* owned output, always sorted ascending (memcmp), no duplicates */

/* One status space for every call. */
typedef enum {
  ZRDT_OK            = 0,
  ZRDT_MISSING       = 1,  /* accept: some links do not resolve; load/check: a link resolves to nothing */
  ZRDT_COLLISION     = 2,  /* two different records with one digest (accept, merge, load) */
  ZRDT_UNREACHABLE   = 3,  /* load/check: a record no head reaches (only possible with hash cycles) */
  ZRDT_NOT_FOUND     = 4,  /* get */
  ZRDT_EMALFORMED    = 5,  /* load: bad magic/version, truncation, trailing bytes, non-canonical order, duplicates */
  ZRDT_ETOOBIG       = 6,  /* an input exceeds a ZRDT_MAX_* bound */
  ZRDT_EMISMATCH     = 7   /* accept_expected: hash(record) != expected */
} zrdt_status;

/* ---- process ---------------------------------------------------------------------------------
   zrdt_init: idempotent; returns 0 on success. Runs the Lean module initialisers and
   lean_io_mark_end_initialization, and turns Lean panics into process exit (fail-stop: a panic
   never yields a silent default value). Process-global side effects are listed in README.

   THREADING: every zrdt_* call in the process, on any store, const or not, must be made from one
   thread at a time (in Electron: synchronously, from the single JS thread that loaded the addon;
   never from AsyncWorker / the libuv threadpool / a worker_threads Worker). Stores share
   immutable inner objects (e.g. after merge) whose reference counts are non-atomic.

   MEMORY: every zrdt_buf / zrdt_digests returned is owned by the caller and must be released with
   zrdt_free_buf / zrdt_free_digests, on every status; outputs not produced are {NULL, 0}, and
   freeing {NULL, 0} is a no-op. No Lean object ever escapes to the caller. */
int         zrdt_init(void);
uint32_t    zrdt_abi_version(void);           /* == ZRDT_ABI_VERSION */
const char *zrdt_impl(void);                  /* "lean-<git sha>" or "stub-<git sha>" */
void        zrdt_free_buf(zrdt_buf);
void        zrdt_free_digests(zrdt_digests);

/* ---- records ---------------------------------------------------------------------------------
   links may be in any order and contain duplicates; the library sorts and deduplicates them
   (the record's links are a set). */
zrdt_status zrdt_payload(uint64_t sender_timestamp, zrdt_bytes body,
                         const zrdt_bytes *attachment_digests, size_t natt, zrdt_buf *out);
zrdt_status zrdt_hash(zrdt_bytes payload, const zrdt_digest *links, size_t nlinks,
                      const zrdt_aci *author, zrdt_digest *out);

/* ---- stores ------------------------------------------------------------------------------ */
zrdt_store *zrdt_store_new(void);
void        zrdt_store_free(zrdt_store *);    /* NULL ok */
size_t      zrdt_count(const zrdt_store *);

typedef struct {
  zrdt_status  status;    /* OK, MISSING, COLLISION, ETOOBIG, EMISMATCH */
  zrdt_digest  digest;    /* hash of the offered record whenever it could be computed (all but ETOOBIG) */
  zrdt_digests missing;   /* MISSING: every unresolved link (sorted, non-empty); otherwise {NULL,0} */
} zrdt_accept_result;
/* OK: inserted, or already present (idempotent). Store unchanged on every other status.
   Order of tests: ETOOBIG, then (accept_expected) EMISMATCH, then MISSING, then COLLISION. */
zrdt_accept_result zrdt_accept(zrdt_store *, zrdt_bytes payload, const zrdt_digest *links,
                               size_t nlinks, const zrdt_aci *author);
/* For ZrdtResend: refuses (EMISMATCH) unless hash(record) == *expected. */
zrdt_accept_result zrdt_accept_expected(zrdt_store *, zrdt_bytes payload, const zrdt_digest *links,
                                        size_t nlinks, const zrdt_aci *author,
                                        const zrdt_digest *expected);

zrdt_digests zrdt_heads(const zrdt_store *);             /* sorted */
zrdt_digests zrdt_all_digests(const zrdt_store *);       /* sorted; for export / re-fetch */

/* Persistence. zrdt_load = decode + check: it returns a store only if the blob is well formed and
   the decoded records are Complete and Tight from their own heads; otherwise NULL, *status says
   why and *where names the smallest offending digest (MISSING / UNREACHABLE / COLLISION).
   Every zrdt_store that exists therefore satisfies the refinement invariant (closed). */
zrdt_status zrdt_save(const zrdt_store *, zrdt_buf *out);  /* canonical: equal stores -> equal bytes */
zrdt_store *zrdt_load(zrdt_bytes blob, zrdt_status *status, zrdt_digest *where);
zrdt_status zrdt_check(const zrdt_store *, zrdt_digest *where);  /* diagnostics; OK for every loaded store */

/* New store = union; inputs unchanged. On COLLISION *out = NULL and *collision is the smallest such digest. */
zrdt_status zrdt_merge(const zrdt_store *a, const zrdt_store *b, zrdt_store **out, zrdt_digest *collision);

/* ---- queries ----------------------------------------------------------------------------- */
int         zrdt_has(const zrdt_store *, const zrdt_digest *);
int         zrdt_reaches(const zrdt_store *, const zrdt_digest *from, const zrdt_digest *to);
zrdt_status zrdt_get(const zrdt_store *, const zrdt_digest *, zrdt_buf *payload,
                     zrdt_digests *links, zrdt_aci *author);       /* OK or NOT_FOUND */
/* Authors (16-byte ACIs, sorted, concatenated) having some record that reaches d ("seen by"). */
zrdt_status zrdt_seen_by(const zrdt_store *, const zrdt_digest *d, zrdt_buf *acis);
/* Pairs (a,b), a<b, of distinct records with equal author and equal links ("fork marker"),
   flattened as 2*k digests, sorted. */
zrdt_digests zrdt_equivocations(const zrdt_store *);

#ifdef __cplusplus
}
#endif
#endif
