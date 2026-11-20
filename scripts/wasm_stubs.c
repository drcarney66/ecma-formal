// The Worker build has the Lean runtime alone, not the Lean library (nix/lean-wasm): what the program names of
// the library is given here. Snapshots (lean/Engine/Cli/Run.lean) are written and read by the library's
// compacted regions, which the Worker build does not have: writing one fails, and none is found to read.
#include <lean/lean.h>

void lean_initialize_runtime_module(void);

void lean_initialize(void) { lean_initialize_runtime_module(); }

lean_object *runtime_initialize_Lean_CompactedRegion(uint8_t builtin) { return lean_io_result_mk_ok(lean_box(0)); }

static lean_object *no_regions(void) {
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("no snapshots in this build")));
}

lean_object *lean_compacted_region_save(b_lean_obj_arg fname, b_lean_obj_arg key, b_lean_obj_arg data,
                                        b_lean_obj_arg deps, lean_obj_arg prev, uint8_t closures) {
  return no_regions();
}

lean_object *lean_compacted_region_read(b_lean_obj_arg fname, b_lean_obj_arg deps) { return no_regions(); }
