use std::convert::TryInto;
use hax_lib as hax;

const BLOCK_SIZE: usize = 64;
const LEN_SIZE: usize = 8;
pub const K_SIZE: usize = 64;
pub const HASH_SIZE: usize = 256 / 8;

pub type Block = [u8; BLOCK_SIZE];
pub type OpTableType = [u8; 12];
pub type Sha256Digest = [u8; HASH_SIZE];
pub type RoundConstantsTable = [u32; K_SIZE];
pub type Hash = [u32; LEN_SIZE];

#[hax::fstar::before("open Spec_Sha256")]

fn from_be_bytes_u32(bytes: [u8; 4]) -> u32 {
    (bytes[0] as u32) << 24 
        | (bytes[1] as u32) << 16
        | (bytes[2] as u32) << 8
        | bytes[3] as u32
}

fn to_be_bytes_u32(n: u32) -> [u8; 4] {
    [
        (n >> 24) as u8,
        (n >> 16) as u8,
        (n >> 8) as u8,
        n as u8,
    ]
}

fn to_be_bytes_u64(n: u64) -> [u8; 8] {
    [
        (n >> 56) as u8,
        (n >> 48) as u8,
        (n >> 40) as u8,
        (n >> 32) as u8,
        (n >> 24) as u8,
        (n >> 16) as u8,
        (n >> 8) as u8,
        n as u8,
    ]
}

// #[hax_lib::requires(0 < n && n < 32)]
#[hax::ensures(|result| fstar!("f_ROTR $n $x = $result"))]
fn rotate_right_u32(x: u32, n: u32) -> u32 {
    // (x >> n) | (x << (32 - n))
    x.rotate_right(n)
}

#[hax::ensures(|result| fstar!("f_ch $x $y $z = $result"))]
pub fn ch(x: u32, y: u32, z: u32) -> u32 {
    (x & y) ^ ((!x) & z)
}

#[hax::ensures(|result| fstar!("f_maj $x $y $z = $result"))]
pub fn maj(x: u32, y: u32, z: u32) -> u32 {
    (x & y) ^ ((x & z) ^ (y & z))
}

const OP_TABLE: OpTableType = [2u8, 13u8, 22u8, 6u8, 11u8, 25u8, 7u8, 18u8, 3u8, 17u8, 19u8, 10u8];

#[rustfmt::skip]
const K_TABLE: RoundConstantsTable = [
    0x428a_2f98u32, 0x7137_4491u32, 0xb5c0_fbcfu32, 0xe9b5_dba5u32, 0x3956_c25bu32,
    0x59f1_11f1u32, 0x923f_82a4u32, 0xab1c_5ed5u32, 0xd807_aa98u32, 0x1283_5b01u32,
    0x2431_85beu32, 0x550c_7dc3u32, 0x72be_5d74u32, 0x80de_b1feu32, 0x9bdc_06a7u32,
    0xc19b_f174u32, 0xe49b_69c1u32, 0xefbe_4786u32, 0x0fc1_9dc6u32, 0x240c_a1ccu32,
    0x2de9_2c6fu32, 0x4a74_84aau32, 0x5cb0_a9dcu32, 0x76f9_88dau32, 0x983e_5152u32,
    0xa831_c66du32, 0xb003_27c8u32, 0xbf59_7fc7u32, 0xc6e0_0bf3u32, 0xd5a7_9147u32,
    0x06ca_6351u32, 0x1429_2967u32, 0x27b7_0a85u32, 0x2e1b_2138u32, 0x4d2c_6dfcu32,
    0x5338_0d13u32, 0x650a_7354u32, 0x766a_0abbu32, 0x81c2_c92eu32, 0x9272_2c85u32,
    0xa2bf_e8a1u32, 0xa81a_664bu32, 0xc24b_8b70u32, 0xc76c_51a3u32, 0xd192_e819u32,
    0xd699_0624u32, 0xf40e_3585u32, 0x106a_a070u32, 0x19a4_c116u32, 0x1e37_6c08u32,
    0x2748_774cu32, 0x34b0_bcb5u32, 0x391c_0cb3u32, 0x4ed8_aa4au32, 0x5b9c_ca4fu32,
    0x682e_6ff3u32, 0x748f_82eeu32, 0x78a5_636fu32, 0x84c8_7814u32, 0x8cc7_0208u32,
    0x90be_fffau32, 0xa450_6cebu32, 0xbef9_a3f7u32, 0xc671_78f2u32
];

const HASH_INIT: Hash = [
    0x6a09e667u32,
    0xbb67ae85u32,
    0x3c6ef372u32,
    0xa54ff53au32,
    0x510e527fu32,
    0x9b05688cu32,
    0x1f83d9abu32,
    0x5be0cd19u32,
];

#[hax_lib::fstar::options("--z3rlimit 60")]
#[hax_lib::requires(i < 4)]
#[hax_lib::ensures(|result| fstar!("f_sigma $x $i =. $result"))]
pub fn sigma(x: u32, i: usize) -> u32 {
    let tmp = if i == 2 || i == 3 {
        x >> OP_TABLE[3 * i + 2]
    } else {
        // x.rotate_right(OP_TABLE[3 * i + 2].into())
        rotate_right_u32(x, OP_TABLE[3 * i + 2].into())
    };

    let rot_val_1 = OP_TABLE[3 * i].into();
    let rot_val_2 = OP_TABLE[3 * i + 1].into();
    // TODO: Add a lemma for associativity and commutativity of xor
    rotate_right_u32(x, rot_val_1) ^ rotate_right_u32(x, rot_val_2) ^ tmp
}

#[hax_lib::fstar::options("--fuel 5 --ifuel 5 --query_stats")]
// #[hax_lib::fstar::verification_status(panic_free)]
// #[hax_lib::ensures(|result| fstar!("f_parse_message_block $block == $result"))]
fn to_be_u32s(block: Block) -> [u32; 16] {
    let mut out = [0; 16];
    for i in 0..16 {
        hax_lib::loop_invariant!(|i: usize| fstar!("
            $out == f_parse_message_block_n $block $out (mk_usize 16) $i
        "));
        let bytes = [
            block[i * 4],
            block[i * 4 + 1],
            block[i * 4 + 2],
            block[i * 4 + 3],
        ];
        out[i] = u32::from_be_bytes(bytes);
    }
    out
}

// #[hax_lib::fstar::options("--fuel 10 --ifuel 10 --z3rlimit 60")]
// #[hax_lib::ensures(|result| fstar!("f_schedule $block == $result"))]
pub fn schedule(block: Block) -> RoundConstantsTable {
    let b = to_be_u32s(block);
    let mut s = [0; K_SIZE];
    for i in 0..K_SIZE {
        hax_lib::loop_invariant!(|i: usize| b.len() == 16);
        if i < 16 {
            s[i] = b[i];
        } else {
            let t16 = s[i - 16];
            let t15 = s[i - 15];
            let t7 = s[i - 7];
            let t2 = s[i - 2];
            let s1 = sigma(t2, 3);
            let s0 = sigma(t15, 2);
            s[i] = s1.wrapping_add(t7).wrapping_add(s0).wrapping_add(t16);
        }
    }
    s
}

// TODO: Take the body out and prove match. Maybe unroll
// Intermediate spec in F* with 3 functions
// hax_lib::loop_invariant!(|i: usize| b.len() == 16);
// wrapping add might need a lemma
// maybe we can remove the ensures from maj, ch etc. 
// harder to debug but more automation
// is unrolling the loop possible?

#[hax_lib::fstar::options("--fuel 1")]
#[hax_lib::ensures(|_| fstar!("f_shuffle $ws ${hash} == ${hash}_future"))]
pub fn shuffle(ws: RoundConstantsTable, hash: &mut Hash) {
    #[cfg(hax)]
    let _hash0: Hash = hash.clone();

    for i in 0..K_SIZE {
        hax_lib::loop_invariant!(|i: usize| fstar!("
            f_shuffle $ws $_hash0 == f_shuffle_rec $ws $hash $i"
        ));

        let a0 = hash[0];
        let b0 = hash[1];
        let c0 = hash[2];
        let d0 = hash[3];
        let e0 = hash[4];
        let f0 = hash[5];
        let g0 = hash[6];
        let h0: u32 = hash[7];

        let t1 = h0
            .wrapping_add(sigma(e0, 1))
            .wrapping_add(ch(e0, f0, g0))
            .wrapping_add(K_TABLE[i])
            .wrapping_add(ws[i]);
        let t2 = sigma(a0, 0)
            .wrapping_add(maj(a0, b0, c0));

        hash[0] = t1.wrapping_add(t2);
        hash[1] = a0;
        hash[2] = b0;
        hash[3] = c0;
        hash[4] = d0.wrapping_add(t1);
        hash[5] = e0;
        hash[6] = f0;
        hash[7] = g0;
    }
}

pub fn compress(block: Block, hash: &mut Hash) {
    let s = schedule(block);
    let h_in = hash.clone();
    shuffle(s, hash);
    for i in 0..8 {
        hash[i] = hash[i].wrapping_add(h_in[i]);
    }
}

fn u32s_to_be_bytes(state: Hash) -> Sha256Digest {
    let mut out: Sha256Digest = [0u8; HASH_SIZE];
    for i in 0..LEN_SIZE {
        let tmp = state[i];
        // let tmp = tmp.to_be_bytes();
        let tmp = to_be_bytes_u32(tmp);
        for j in 0..4 {
            out[i * 4 + j] = tmp[j];
        }
    }
    out
}

#[hax_lib::requires((msg.len() as u64) < 0x1fffffffffffffff)]
pub fn hash(msg: &[u8]) -> Sha256Digest {
    let mut h = HASH_INIT;
    let blocks = msg.len() / BLOCK_SIZE;
    for i in 0..blocks {
        compress(
            msg[i * BLOCK_SIZE..(i + 1) * BLOCK_SIZE]
                .try_into()
                .unwrap(),
            &mut h,
        );
    }

    let last_block_len = msg.len() % BLOCK_SIZE;
    let mut last_block: Block = [0; BLOCK_SIZE];
    last_block[0..last_block_len].copy_from_slice(&msg[blocks * BLOCK_SIZE..]);
    last_block[last_block_len] = 0x80;
    hax_lib::fstar!("assert(Seq.length msg * 8 < pow2 64)");
    let len_bist = msg.len() as u64 * 8;
    // let len_bist_bytes = len_bist.to_be_bytes();
    let len_bist_bytes = to_be_bytes_u64(len_bist);
    if last_block_len < BLOCK_SIZE - LEN_SIZE {
        for i in 0..LEN_SIZE {
            last_block[BLOCK_SIZE - LEN_SIZE + i] = len_bist_bytes[i];
        }
        compress(last_block, &mut h);
    } else {
        let mut pad_block: Block = [0; BLOCK_SIZE];
        for i in 0..LEN_SIZE {
            pad_block[BLOCK_SIZE - LEN_SIZE + i] = len_bist_bytes[i];
        }
        compress(last_block, &mut h);
        compress(pad_block, &mut h);
    }

    u32s_to_be_bytes(h)
}

#[hax_lib::requires((msg.len() as u64) < 0x1fffffffffffffff)]
pub fn sha256(msg: &[u8]) -> Sha256Digest {
    hash(msg)
}
