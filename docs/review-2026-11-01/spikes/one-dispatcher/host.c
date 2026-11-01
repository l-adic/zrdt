/* everything the N-API glue would need in C: no store handles, no refcount games beyond one call */
#include <lean/lean.h>
#include <stdio.h>
#include <string.h>
lean_object* initialize_Zv(uint8_t builtin);
lean_object* zrdt_l_call(lean_object*);
static int zinit(void){
  lean_initialize_runtime_module(); lean_set_panic_messages(false);
  lean_object* r = initialize_Zv(1); if (lean_io_result_is_error(r)) return -1; lean_dec_ref(r);
  lean_io_mark_end_initialization(); return 0; }
/* bytes in -> bytes out; returns length or -1 */
static long zcall(const unsigned char* in, size_t n, unsigned char* out, size_t cap){
  lean_object* a = lean_alloc_sarray(1, n, n); memcpy(lean_sarray_cptr(a), in, n);
  lean_object* r = zrdt_l_call(a);                      /* consumes a */
  if (lean_io_result_is_error(r)) { lean_dec_ref(r); return -1; }
  lean_object* v = lean_io_result_get_value(r);
  size_t m = lean_sarray_size(v); long rc = m <= cap ? (memcpy(out, lean_sarray_cptr(v), m), (long)m) : -1;
  lean_dec_ref(r); return rc; }
int main(void){
  if (zinit()) return 1; unsigned char o[16], q[] = {1,'h','i'}, c[] = {2};
  for (int i = 0; i < 3; i++) zcall(q, 3, o, 16);
  long m = zcall(c, 1, o, 16); printf("count reply len %ld: %d %d\n", m, o[0], o[1]); return 0; }
