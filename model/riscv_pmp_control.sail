/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* address ranges */

// [min, max) of the matching range, in units of 4 bytes.
type pmp_addr_range_in_words = option((int, int))

function pmpAddrRange(cfg: Pmpcfg_ent, pmpaddr: xlenbits, prev_pmpaddr: xlenbits) -> pmp_addr_range_in_words = {
  match pmpAddrMatchType_of_bits(cfg[A]) {
    OFF   => None(),
    TOR   => { Some ((unsigned(prev_pmpaddr), unsigned(pmpaddr))) },
    NA4   => {
               // NA4 is not selectable when the PMP grain G >= 1. See pmpWriteCfg().
               assert(sys_pmp_grain() < 1, "NA4 cannot be selected when PMP grain G >= 1.");
               let lo = unsigned(pmpaddr);
               Some((lo, lo + 1))
             },
    NAPOT => {
               // Example pmpaddr: 0b00010101111
               //                          ^--- last 0 dictates region size & alignment
               let mask = pmpaddr ^ (pmpaddr + 1);
               // pmpaddr + 1:     0b00010110000
               // mask:            0b00000011111
               // ~mask:           0b11111100000
               let lo   = pmpaddr & (~ (mask));
               // mask + 1:        0b00000100000
               let len  = unsigned(mask) + 1;
               Some((unsigned(lo), (unsigned(lo) + len)))
             }
  }
}

/* permission checks */

val pmpCheckRWX: (Pmpcfg_ent, AccessType(ext_access_type)) -> bool
function pmpCheckRWX(ent, acc) = {
  match acc {
    Read(_)      => ent[R] == 0b1,
    Write(_)     => ent[W] == 0b1,
    ReadWrite(_) => ent[R] == 0b1 & ent[W] == 0b1,
    Execute()    => ent[X] == 0b1
  }
}

/* this needs to be called with the effective current privilege */
val pmpCheckPerms: (Pmpcfg_ent, AccessType(ext_access_type), Privilege) -> bool effect {rreg}
function pmpCheckPerms(ent, acc, priv) = {
  match mseccfg.MML() {
    0b1 =>
      match (ent.L(), ent.R(), ent.W(), ent.X()) {
        (0b1, 0b0, 0b1, _) =>
          match acc {
            Execute(_) => true,
            Read(_)    => priv == Machine & ent.X() == 0b1,
            _          => false
          },
        (0b0, 0b0, 0b1, _) =>
          match acc {
            Read(_)  => true,
            Write(_) => priv == Machine | ent.X() == 0b1,
            _        => false
          },
        (0b1, 0b1, 0b1, 0b1) =>
          match acc {
            Read(_) => true,
            _       => false
          },
        (_, _, _, _) =>
          if (priv == Machine) == pmpLockBit(ent)
          then pmpCheckRWX(ent, acc)
          else false
      },
    0b0 =>
      match priv {
        Machine =>
          if pmpLockBit(ent)
          then pmpCheckRWX(ent, acc)
          else true,
        _       => pmpCheckRWX(ent, acc)
      }
  }
}

/* matching logic */

enum pmpAddrMatch = {PMP_NoMatch, PMP_PartialMatch, PMP_Match}

function pmpMatchAddr(addr: int, width: int, rng: pmp_addr_range_in_words) -> pmpAddrMatch = {
  match rng {
    None()         => PMP_NoMatch,
    Some((lo, hi)) => {
      // Convert to integers.
      // These are in units of 4 bytes.
      let lo = lo * 4;
      let hi = hi * 4;

      if   hi <= lo   /* to handle mis-configuration */
      then PMP_NoMatch
      else {
        if      (addr + width <= lo) | (hi <= addr)
        then    PMP_NoMatch
        else if (lo <= addr) & (addr + width <= hi)
        then    PMP_Match
        else    PMP_PartialMatch
      }
    },
  }
}

enum pmpMatch = {PMP_Success, PMP_Continue, PMP_Fail}

function pmpMatchEntry(addr: int, width: int, acc: AccessType(ext_access_type), priv: Privilege,
                       ent: Pmpcfg_ent, pmpaddr: xlenbits, prev_pmpaddr: xlenbits) -> pmpMatch = {
  let rng = pmpAddrRange(ent, pmpaddr, prev_pmpaddr);
  match pmpMatchAddr(addr, width, rng) {
    PMP_NoMatch      => PMP_Continue,
    PMP_PartialMatch => PMP_Fail,
    PMP_Match        => if   pmpCheckPerms(ent, acc, priv)
                        then PMP_Success
                        else PMP_Fail
  }
}

/* priority checks */

function pmpCheck forall 'n, 'n > 0. (addr: xlenbits, width: atom('n), acc: AccessType(ext_access_type), priv: Privilege)
                  -> option(ExceptionType) = {
  let width : xlenbits = to_bits(sizeof(xlen), width);
  let check : bool =
  match pmpMatchEntry(addr, width, acc, priv, pmp0cfg, pmpaddr0, zeros()) {
    PMP_Success  => true,
    PMP_Fail     => false,
    PMP_Continue =>
  match pmpMatchEntry(addr, width, acc, priv, pmp1cfg, pmpaddr1, pmpaddr0) {
    PMP_Success  => true,
    PMP_Fail     => false,
    PMP_Continue =>
  match pmpMatchEntry(addr, width, acc, priv, pmp2cfg, pmpaddr2, pmpaddr1) {
    PMP_Success  => true,
    PMP_Fail     => false,
    PMP_Continue =>
  match pmpMatchEntry(addr, width, acc, priv, pmp3cfg, pmpaddr3, pmpaddr2) {
    PMP_Success  => true,
    PMP_Fail     => false,
    PMP_Continue =>
  match pmpMatchEntry(addr, width, acc, priv, pmp4cfg, pmpaddr4, pmpaddr3) {
    PMP_Success  => true,
    PMP_Fail     => false,
    PMP_Continue =>
  match pmpMatchEntry(addr, width, acc, priv, pmp5cfg, pmpaddr5, pmpaddr4) {
    PMP_Success  => true,
    PMP_Fail     => false,
    PMP_Continue =>
  match pmpMatchEntry(addr, width, acc, priv, pmp6cfg, pmpaddr6, pmpaddr5) {
    PMP_Success  => true,
    PMP_Fail     => false,
    PMP_Continue =>
  match pmpMatchEntry(addr, width, acc, priv, pmp7cfg, pmpaddr7, pmpaddr6) {
    PMP_Success  => true,
    PMP_Fail     => false,
    PMP_Continue =>
  match pmpMatchEntry(addr, width, acc, priv, pmp8cfg, pmpaddr8, pmpaddr7) {
    PMP_Success  => true,
    PMP_Fail     => false,
    PMP_Continue =>
  match pmpMatchEntry(addr, width, acc, priv, pmp9cfg, pmpaddr9, pmpaddr8) {
    PMP_Success  => true,
    PMP_Fail     => false,
    PMP_Continue =>
  match pmpMatchEntry(addr, width, acc, priv, pmp10cfg, pmpaddr10, pmpaddr9) {
    PMP_Success  => true,
    PMP_Fail     => false,
    PMP_Continue =>
  match pmpMatchEntry(addr, width, acc, priv, pmp11cfg, pmpaddr11, pmpaddr10) {
    PMP_Success  => true,
    PMP_Fail     => false,
    PMP_Continue =>
  match pmpMatchEntry(addr, width, acc, priv, pmp12cfg, pmpaddr12, pmpaddr11) {
    PMP_Success  => true,
    PMP_Fail     => false,
    PMP_Continue =>
  match pmpMatchEntry(addr, width, acc, priv, pmp13cfg, pmpaddr13, pmpaddr12) {
    PMP_Success  => true,
    PMP_Fail     => false,
    PMP_Continue =>
  match pmpMatchEntry(addr, width, acc, priv, pmp14cfg, pmpaddr14, pmpaddr13) {
    PMP_Success  => true,
    PMP_Fail     => false,
    PMP_Continue =>
  match pmpMatchEntry(addr, width, acc, priv, pmp15cfg, pmpaddr15, pmpaddr14) {
    PMP_Success  => true,
    PMP_Fail     => false,
    PMP_Continue =>
      match priv {
        Machine =>
          if mseccfg.MMWP() == 0b1                /* Make Read, Write and execute denied by default, if condition meets for M mode */
          then false
          else if mseccfg.MML() == 0b1            /* Make execute denied, if condition meets for M mode */
          then match acc {
                 Execute(_) => false,
                 _          => true
               }
          else true,
        _       => false                          /* Make Read, Write and execute denied by default for S/U mode */
      }
  }}}}}}}}}}}}}}}};

  if   check
  then None()
  else match acc {
    Read(_)      => Some(E_Load_Access_Fault()),
    Write(_)     => Some(E_SAMO_Access_Fault()),
    ReadWrite(_) => Some(E_SAMO_Access_Fault()),
    Execute()    => Some(E_Fetch_Access_Fault())
  }

function init_pmp() -> unit = {
  mseccfg->RLB() = 0b0;
  mseccfg->MML() = 0b0;
  mseccfg->MMWP() = 0b0;
  mseccfgh = zero_extend(0b0);
  foreach (i from 0 to 63) {
    // On reset the PMP register's A and L bits are set to 0 unless the plaform
    // mandates a different value.
    pmpcfg_n[i] = [pmpcfg_n[i] with A = pmpAddrMatchType_to_bits(OFF), L = 0b0];
  };
}
