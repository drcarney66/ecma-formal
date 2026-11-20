// Initializes the runtime, Init and Std, as a Lean program's main does.
#include <lean/lean.h>

void lean_initialize_runtime_module(void);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Std(uint8_t builtin);

static int ok(lean_object* res) {
  if (lean_io_result_is_error(res)) return 0;
  lean_dec_ref(res);
  return 1;
}

int main(void) {
  lean_initialize_runtime_module();
  lean_set_panic_messages(false);
  if (!ok(initialize_Init(1)) || !ok(initialize_Std(1))) return 1;
  lean_set_panic_messages(true);
  lean_io_mark_end_initialization();
  return 0;
}
