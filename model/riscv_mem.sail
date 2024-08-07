/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* Physical memory model.
 *
 * This assumes that the platform memory map has been defined, so that accesses
 * to MMIO regions can be dispatched.
 *
 * The implementation below supports the reading and writing of memory
 * metadata in addition to raw memory data.
 *
 * The external API for this module is composed of three central functions
 *
 *   mem_read_priv_meta
 *   mem_write_ea
 *   mem_write_value_priv_meta
 *
 * and some special cases which partially apply these functions:
 *
 *   mem_read_priv - strips metadata from reads
 *   mem_read_meta - uses effectivePrivilege
 *   mem_read      - both of the above partial applications
 *
 *   mem_write_value_meta - uses effectivePrivilege
 *   mem_write_value_priv - uses a default value for metadata
 *   mem_write_value      - both of the above partial applications
 *
 * The internal implementation first performs a PMP check (if PMP is
 * enabled), and then dispatches to MMIO regions or physical memory as
 * per the platform memory map.
 */

function is_aligned_addr forall 'n. (addr : xlenbits, width : int('n)) -> bool =
  unsigned(addr) % width == 0

function read_kind_of_flags (aq : bool, rl : bool, res : bool) -> option(read_kind) =
  match (aq, rl, res) {
    (false, false, false) => Some(Read_plain),
    (true, false, false)  => Some(Read_RISCV_acquire),
    (true, true, false)   => Some(Read_RISCV_strong_acquire),
    (false, false, true)  => Some(Read_RISCV_reserved),
    (true, false, true)   => Some(Read_RISCV_reserved_acquire),
    (true, true, true)    => Some(Read_RISCV_reserved_strong_acquire),
    (false, true, false)  => None(), /* should these be instead throwing error_not_implemented as below? */
    (false, true, true)   => None()
  }

function write_kind_of_flags (aq : bool, rl : bool, con : bool) -> write_kind =
  match (aq, rl, con) {
    (false, false, false) => Write_plain,
    (false, true,  false) => Write_RISCV_release,
    (false, false, true)  => Write_RISCV_conditional,
    (false, true , true)  => Write_RISCV_conditional_release,
    (true,  true,  false) => Write_RISCV_strong_release,
    (true,  true , true)  => Write_RISCV_conditional_strong_release,
    // throw an illegal instruction here?
    (true,  false, false) => throw(Error_not_implemented("store.aq")),
    (true,  false, true)  => throw(Error_not_implemented("sc.aq"))
  }

// only used for actual memory regions, to avoid MMIO effects
function phys_mem_read_word_aligned (t : AccessType(ext_access_type), paddr : xlenbits, aq: bool, rl: bool, res: bool) -> MemoryOpResult(bits(32)) = {
  let result = (match read_kind_of_flags(aq, rl, res) {
    Some(rk) => Some(read_ram(rk, paddr)),
    None()   => None()
  }) : option(bits(32));
  match (t, result) {
    (Execute(),  None()) => MemException(paddr, E_Fetch_Access_Fault()),
    (Read(Data), None()) => MemException(paddr, E_Load_Access_Fault()),
    (_,          None()) => MemException(paddr, E_SAMO_Access_Fault()),
    (_,      Some(v)) => { if   get_config_print_mem()
                              then print_mem("mem[" ^ to_str(t) ^ "," ^ BitStr(paddr) ^ "] -> " ^ BitStr(v));
                              MemValue(v) }
  }
}

function extract_bits forall 'n, 0 < 'n <= max_mem_access . (value : bits(64), addroff: bits(2), width: int('n)) -> bits(8 * 'n) =
  if width == 8 then value
  else {
    assert(width <= 4);
    match addroff {
      0b00 => value[width*8 - 1..0],
      0b01 => value[width*8 - 1 + 8..8],
      0b10 => value[width*8 - 1 + 16..16],
      0b11 => value[width*8 - 1 + 24..24],
    }
  }

/* Does either 1 or 2 memory accesses based on alignment and width */
function checked_mem_read forall 'n, 0 < 'n <= max_mem_access . (
  t : AccessType(ext_access_type),
  priv : Privilege,
  paddr : xlenbits,
  width : int('n),
  aq : bool,
  rl : bool,
  res: bool
) -> MemoryOpResult((bits(8 * 'n), mem_meta)) = {
  let aligned = [paddr with 1..0 = 0b00];
  let aligned_next = aligned + zero_extend(0x4);

  let meta = __ReadRAM_Meta(paddr, width);

  let res_fst = (match pmpCheck(unsigned(aligned), 4, t, priv) {
    Some(e) => MemException(paddr, e), // Use misaligned version
    None() => phys_mem_read_word_aligned(t, aligned, aq, rl, res),
  }) : MemoryOpResult(bits(32));

  if 4 - unsigned(paddr[1..0]) < width then {
    let res_snd = (match pmpCheck(unsigned(aligned_next), 4, t, priv) {
      Some(e) => MemException(aligned_next, e),
      None() => phys_mem_read_word_aligned(t, aligned_next, aq, rl, res),
    }) : MemoryOpResult(bits(32));

    match (res_fst, res_snd) {
      (MemException(a, e), _) => MemException(a, e),
      (MemValue(_), MemException(a, e)) => MemException(a, e),
      (MemValue(v1), MemValue(v2)) => MemValue((extract_bits(v2 @ v1, paddr[1..0], width), meta))
    }
  } else
    match res_fst {
      MemException(a, e) => MemException(a, e),
      MemValue(v) => MemValue((extract_bits(0x00000000 @ v, paddr[1..0], width), meta))
    }
}

/* Atomic accesses can be done to MMIO regions, e.g. in kernel access to device registers. */

$ifdef RVFI_DII
val rvfi_read : forall 'n, 'n > 0. (xlenbits, int('n), MemoryOpResult((bits(8 * 'n), mem_meta))) -> unit
function rvfi_read (addr, width, result) = {
  rvfi_mem_data[rvfi_mem_addr] = zero_extend(addr);
  rvfi_mem_data_present = true;
  match result {
    /* TODO: report tag bit for capability writes and extend mask by one bit. */
    MemValue(v, _) => if width <= 16
                       then { rvfi_mem_data[rvfi_mem_rdata] = sail_zero_extend(v, 256);
                              rvfi_mem_data[rvfi_mem_rmask] = rvfi_encode_width_mask(width) }
                       else { internal_error(__FILE__, __LINE__, "Expected at most 16 bytes here!") },
    MemException(_, _) => ()
  };
}
$else
val rvfi_read : forall 'n, 'n > 0. (xlenbits, int('n), MemoryOpResult((bits(8 * 'n), mem_meta))) -> unit
function rvfi_read (addr, width, result) = ()
$endif

val mem_read      : forall 'n, 0 < 'n <= max_mem_access . (AccessType(ext_access_type), xlenbits, int('n), bool, bool, bool) -> MemoryOpResult(bits(8 * 'n))
val mem_read_meta : forall 'n, 0 < 'n <= max_mem_access . (AccessType(ext_access_type), xlenbits, int('n), bool, bool, bool) -> MemoryOpResult((bits(8 * 'n), mem_meta))
val mem_read_priv_meta : forall 'n, 0 < 'n <= max_mem_access . (AccessType(ext_access_type), Privilege, xlenbits, int('n), bool, bool, bool) -> MemoryOpResult((bits(8 * 'n), mem_meta))
val mem_read_i      : forall 'n, 0 < 'n <= max_mem_access . (AccessType(ext_access_type), xlenbits, int('n)) -> MemoryOpResult(unit)

/* The most generic memory read operation */
function mem_read_priv_meta (typ, priv, paddr, width, aq, rl, res) = {
  let result : MemoryOpResult((bits(8 * 'n), mem_meta)) =
    if (aq | res) & not(is_aligned_addr(paddr, width))
    then MemException(paddr, E_Load_Addr_Align())
    else match (aq, rl, res) {
      (false, true,  false) => throw(Error_not_implemented("load.rl")),
      (false, true,  true)  => throw(Error_not_implemented("lr.rl")),
      (_, _, _)             => checked_mem_read(typ, priv, paddr, width, aq, rl, res)
    };
  result
}

/* Specialized mem_read_priv that operates at the default effective privilege */
function mem_read (typ, paddr, width, aq, rel, res) =
  match mem_read_priv_meta(typ, effectivePrivilege(typ, mstatus, cur_privilege), paddr, width, aq, rel, res) {
    MemValue(v, _) => MemValue(v),
    MemException(a, b) => MemException(a, b)
  }

function mem_read_meta (typ, paddr, width, aq, rel, res) =
  mem_read_priv_meta(typ, effectivePrivilege(typ, mstatus, cur_privilege), paddr, width, aq, rel, res)

function mem_read_i (t, paddr, width) = {
  let priv = effectivePrivilege(t, mstatus, cur_privilege);

  let aligned = [paddr with 1..0 = 0b00];
  let aligned_next = aligned + zero_extend(0x4);

  match pmpCheck(unsigned(aligned), 4, t, priv) {
    Some(e) => MemException(paddr, e),
    None() =>
      if (width == 2) | (paddr[1..0] == 0b00)
      then MemValue(())
      else match pmpCheck(unsigned(aligned_next), 4, t, priv) {
        Some(e) => MemException(paddr + zero_extend(0x2), e),
        None() => MemValue(()),
      }
  }
}

val mem_write_ea : forall 'n, 0 < 'n <= max_mem_access . (xlenbits, int('n), bool, bool, bool) -> MemoryOpResult(unit)
function mem_write_ea (addr, width, aq, rl, con) =
  if (rl | con) & not(is_aligned_addr(addr, width))
  then MemException(addr, E_SAMO_Addr_Align())
  else MemValue(write_ram_ea(write_kind_of_flags(aq, rl, con), addr, width))

$ifdef RVFI_DII
val rvfi_write : forall 'n, 0 < 'n <= max_mem_access . (xlenbits, int('n), bits(8 * 'n), mem_meta, MemoryOpResult(bool)) -> unit
function rvfi_write (addr, width, value, meta, result) = {
  rvfi_mem_data[rvfi_mem_addr] = zero_extend(addr);
  rvfi_mem_data_present = true;
  match result {
    /* Log only the memory address (without the value) if the write fails. */
    MemValue(_) => if width <= 16 then {
        /* TODO: report tag bit for capability writes and extend mask by one bit. */
        rvfi_mem_data[rvfi_mem_wdata] = sail_zero_extend(value,256);
        rvfi_mem_data[rvfi_mem_wmask] = rvfi_encode_width_mask(width);
      } else {
        internal_error(__FILE__, __LINE__, "Expected at most 16 bytes here!");
      },
    MemException(_, _) => ()
  }
}
$else
val rvfi_write : forall 'n, 'n > 0. (xlenbits, int('n), bits(8 * 'n), mem_meta, MemoryOpResult(bool)) -> unit
function rvfi_write (addr, width, value, meta, result) = ()
$endif

function split_bits_byte (value : bits(8), addroff: bits(2)) -> (bits(32), bits(4), bits(32), bits(4)) =
  match addroff {
    0b00 => (0x000000 @ value, 0b0001, 0x00000000, 0b0000),
    0b01 => (0x0000 @ value @ 0x00, 0b0010, 0x00000000, 0b0000),
    0b10 => (0x00 @ value @ 0x0000, 0b0100, 0x00000000, 0b0000),
    0b11 => (value @ 0x000000, 0b1000, 0x00000000, 0b0000),
  }

function split_bits_half (value : bits(16), addroff: bits(2)) -> (bits(32), bits(4), bits(32), bits(4)) =
  match addroff {
    0b00 => (0x0000 @ value, 0b0011, 0x00000000, 0b0000),
    0b01 => (0x00 @ value @ 0x00, 0b0110, 0x00000000, 0b0000),
    0b10 => (value @ 0x0000, 0b1100, 0x00000000, 0b0000),
    0b11 => (value[7..0] @ 0x000000, 0b1000, 0x000000 @ value[15..8], 0b0001),
  }

function split_bits_word (value : bits(32), addroff: bits(2)) -> (bits(32), bits(4), bits(32), bits(4)) =
  match addroff {
    0b00 => (value, 0b1111, 0x00000000, 0b0000),
    0b01 => (value[23..0] @ 0x00, 0b1110, 0x000000 @ value[31..24], 0b0001),
    0b10 => (value[15..0] @ 0x0000, 0b1100, 0x0000 @ value[31..16], 0b0011),
    0b11 => (value[7..0] @ 0x000000, 0b1000, 0x00 @ value[31..8], 0b0111),
  }

// only used for actual memory regions, to avoid MMIO effects
function phys_mem_write_word_aligned (wk : write_kind, paddr : xlenbits, data : bits(32), be : bits(4)) -> MemoryOpResult(bool) = {
  write_ram(wk, paddr, data, be);
  if   get_config_print_mem()
  then print_mem("mem[" ^ BitStr(paddr) ^ "] <- " ^ BitStr(data));
  MemValue(true)
}

/* dispatches to MMIO regions or physical memory regions depending on physical memory map */
function checked_mem_write forall 'n, 0 < 'n <= max_mem_access . (
  paddr : xlenbits,
  width : int('n),
  data: bits(8 * 'n),
  typ : AccessType(ext_access_type),
  priv : Privilege,
  meta: mem_meta,
  aq : bool,
  rl : bool,
  con : bool,
) -> MemoryOpResult(bool) = {
  let aligned = [paddr with 1..0 = 0b00];
  let aligned_next = aligned + zero_extend(0x4);

  __WriteRAM_Meta(paddr, width, meta);

  let wk = write_kind_of_flags(aq, rl, con);

  let (fst_data, fst_be, snd_data, snd_be) = (match width {
    1 => split_bits_byte(data, paddr[1..0]),
    2 => split_bits_half(data, paddr[1..0]),
    4 => split_bits_word(data, paddr[1..0]),
    8 => (data[31..0], 0b1111, data[63..32], 0b1111),
    _ => internal_error(__FILE__, __LINE__, "store got bad width")
  }) : (bits(32), bits(4), bits(32), bits(4));

  let res_fst = (match pmpCheck(unsigned(aligned), 4, typ, priv) {
    Some(e) => MemException(paddr, e), // Use misaligned version
    None() => phys_mem_write_word_aligned(wk, aligned, fst_data, fst_be),
  }) : MemoryOpResult(bool);

  if 4 - unsigned(paddr[1..0]) < width then {
    let res_snd = (match pmpCheck(unsigned(aligned_next), 4, typ, priv) {
      Some(e) => MemException(aligned_next, e),
      None() => phys_mem_write_word_aligned(wk, aligned_next, snd_data, snd_be),
    }) : MemoryOpResult(bool);

    match (res_fst, res_snd) {
      (MemException(a, e), _) => MemException(a, e),
      (MemValue(_), MemException(a, e)) => MemException(a, e),
      (MemValue(_), MemValue(_)) => MemValue(true)
    }
  } else res_fst
}

/* Atomic accesses can be done to MMIO regions, e.g. in kernel access to device registers. */

/* Memory write with an explicit metadata value.  Metadata writes are
 * currently assumed to have the same alignment constraints as their
 * data.
 * NOTE: The wreg effect is due to MMIO, the rreg is due to checking mtime.
 */
val mem_write_value_priv_meta : forall 'n, 0 < 'n <= max_mem_access . (xlenbits, int('n), bits(8 * 'n), AccessType(ext_access_type), Privilege, mem_meta, bool, bool, bool) -> MemoryOpResult(bool)
function mem_write_value_priv_meta (paddr, width, value, typ, priv, meta, aq, rl, con) = {
  if (rl | con) & not(is_aligned_addr(paddr, width))
  then MemException(paddr, E_SAMO_Addr_Align())
  else {
    let result = checked_mem_write(paddr, width, value, typ, priv, meta, aq, rl, con);
    rvfi_write(paddr, width, value, meta, result);
    result
  }
}

/* Memory write with explicit Privilege, implicit AccessType and metadata */
val mem_write_value_priv : forall 'n, 0 < 'n <= max_mem_access . (xlenbits, int('n), bits(8 * 'n), Privilege, bool, bool, bool) -> MemoryOpResult(bool)
function mem_write_value_priv (paddr, width, value, priv, aq, rl, con) =
  mem_write_value_priv_meta(paddr, width, value, Write(default_write_acc), priv, default_meta, aq, rl, con)

/* Memory write with explicit metadata and AccessType, implicit and Privilege */
val mem_write_value_meta : forall 'n, 0 < 'n <= max_mem_access . (xlenbits, int('n), bits(8 * 'n), ext_access_type, mem_meta, bool, bool, bool) -> MemoryOpResult(bool)
function mem_write_value_meta (paddr, width, value, ext_acc, meta, aq, rl, con) = {
  let typ = Write(ext_acc);
  let ep = effectivePrivilege(typ, mstatus, cur_privilege);
  mem_write_value_priv_meta(paddr, width, value, typ, ep, meta, aq, rl, con)
}

/* Memory write with default AccessType, Privilege, and metadata */
val mem_write_value : forall 'n, 0 < 'n <= max_mem_access . (xlenbits, int('n), bits(8 * 'n), bool, bool, bool) -> MemoryOpResult(bool)
function mem_write_value (paddr, width, value, aq, rl, con) = {
  mem_write_value_meta(paddr, width, value, default_write_acc, default_meta, aq, rl, con)
}
