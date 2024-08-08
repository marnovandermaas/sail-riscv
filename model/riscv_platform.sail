/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* Platform-specific definitions. */

/* whether the MMU should update dirty bits in PTEs */
val plat_enable_dirty_update = {ocaml: "Platform.enable_dirty_update",
                                interpreter: "Platform.enable_dirty_update",
                                c: "plat_enable_dirty_update",
                                lem: "plat_enable_dirty_update"} : unit -> bool

/* whether the platform supports misaligned accesses without trapping to M-mode. if false,
 * misaligned loads/stores are trapped to Machine mode.
 */
val plat_enable_misaligned_access = {ocaml: "Platform.enable_misaligned_access",
                                     interpreter: "Platform.enable_misaligned_access",
                                     c: "plat_enable_misaligned_access",
                                     lem: "plat_enable_misaligned_access"} : unit -> bool

/* whether mtval stores the bits of a faulting instruction on illegal instruction exceptions */
val plat_mtval_has_illegal_inst_bits = {ocaml: "Platform.mtval_has_illegal_inst_bits",
                                        interpreter: "Platform.mtval_has_illegal_inst_bits",
                                        c: "plat_mtval_has_illegal_inst_bits",
                                        lem: "plat_mtval_has_illegal_inst_bits"} : unit -> bool

/* whether mtval stores the bits of the ebreak instruction on EBREAK */
val plat_mtval_has_ebreak_pc = {ocaml: "Platform.plat_mtval_has_ebreak_pc",
                                        interpreter: "Platform.plat_mtval_has_ebreak_pc",
                                        c: "plat_mtval_has_ebreak_pc",
                                        lem: "plat_mtval_has_ebreak_pc"} : unit -> bool

/* Platform initialization and ticking. */

function init_platform() -> unit = ()
function tick_platform() -> unit = ()

/* Platform-specific handling of instruction faults */

function handle_illegal() -> unit = {
  let info = if plat_mtval_has_illegal_inst_bits ()
             then Some(instbits)
             else None();
  let t : sync_exception = struct { trap    = E_Illegal_Instr(),
                                    excinfo = info,
                                    ext     = None() };
  set_next_pc(exception_handler(cur_privilege, CTL_TRAP(t), PC))
}

/* Platform-specific wait-for-interrupt */

function platform_wfi() -> unit = {
  cancel_reservation();
}
