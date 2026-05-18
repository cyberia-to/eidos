// stdlib/ids.rs — inductive type IDs and constructor indices
// In production these are hemera hashes of the declaration nouns.
// Here we use small constants for determinism in tests.

pub const NAT_ID:   u64 = 0x4E41_5400;
pub const BOOL_ID:  u64 = 0x424F_4F4C;
pub const LIST_ID:  u64 = 0x4C49_5354;
pub const EQ_ID:    u64 = 0x4551_0000;
pub const FALSE_ID: u64 = 0x4641_4C53;
pub const TRUE_ID:  u64 = 0x5452_5545;
pub const AND_ID:   u64 = 0x414E_4400;
pub const OR_ID:    u64 = 0x4F52_0000;
pub const FIN_ID:   u64 = 0x46494E00;
pub const LE_ID:    u64 = 0x4E4C_4500;  // NatLE

pub const NAT_ZERO: u64 = 0;
pub const NAT_NEXT: u64 = 1;

pub const BOOL_FALSE_IDX: u64 = 0;
pub const BOOL_TRUE_IDX:  u64 = 1;

pub const LIST_NIL_IDX:  u64 = 0;
pub const LIST_LINK_IDX: u64 = 1;

pub const FIN_ZERO_IDX: u64 = 0;
pub const FIN_NEXT_IDX: u64 = 1;

pub const LE_REFL_IDX: u64 = 0;
pub const LE_STEP_IDX: u64 = 1;
