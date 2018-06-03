module Spec.RSA.Test

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.RawIntTypes
open Spec.Lib.IntSeq
open Spec.Lib.Stateful
open FStar.All

open Spec.Bignum.Basic
open Spec.RSA

#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0"

(* RSASSA-PSS test vectors *)
(* https://github.com/pyca/cryptography/blob/master/vectors/cryptography_vectors/asymmetric/RSA/pkcs-1v2-1d2-vec/pss-vect.txt *)
val ctest:
  modBits:size_nat{8*blocks modBits 8 < max_size_t} -> n:lbytes (blocks modBits 8) ->
  eBits:size_nat{8*blocks eBits 8 < max_size_t} -> e:lbytes (blocks eBits 8) ->
  dBits:size_nat{8*blocks dBits 8 < max_size_t} -> d:lbytes (blocks dBits 8) ->
  pBits:size_nat{8*blocks pBits 8 < max_size_t} -> p:lbytes (blocks pBits 8) ->
  qBits:size_nat{8*blocks qBits 8 < max_size_t} -> q:lbytes (blocks qBits 8) ->
  msgLen:size_nat -> msg:lbytes msgLen ->
  sLen:size_nat -> salt:lbytes sLen ->
  rBlind:lbytes 8 ->
  sgnt_expected:lbytes (8*blocks modBits 8) -> num:FStar.UInt8.t ->
  ML bool
let ctest modBits n eBits e dBits d pBits p qBits q msgLen msg sLen salt rBlind sgnt_expected num =
  let n = bn_from_bytes_be #(blocks modBits 8) n in
  let e = bn_from_bytes_be #(blocks eBits 8) e in
  let d = bn_from_bytes_be #(blocks dBits 8) d in
  let p = bn_from_bytes_be #(blocks pBits 8) p in
  let q = bn_from_bytes_be #(blocks qBits 8) q in
  let rBlind = bn_from_bytes_be #8 rBlind in

  let pkey = Mk_rsa_pubkey n e in
  let skey = Mk_rsa_privkey pkey d p q in
  let sgnt_computed = rsapss_sign #sLen #msgLen #eBits modBits dBits pBits qBits skey salt rBlind msg in
  let check = eq_bytes sgnt_computed sgnt_expected in

  let verify = rsapss_verify #msgLen modBits eBits pkey sLen msg sgnt_expected in

  IO.print_string ("\n Test "); IO.print_string (UInt8.to_string (num));
  IO.print_string "\n sgnt_computed \n";
  List.iter (fun a -> IO.print_string (UInt8.to_string_hex (u8_to_UInt8 a))) (as_list sgnt_computed);
  IO.print_string "\n sgnt_expected \n";
  List.iter (fun a -> IO.print_string (UInt8.to_string_hex (u8_to_UInt8 a))) (as_list sgnt_expected);
  IO.print_string "\n";
  check && verify

val test1: unit -> ML bool
let test1() =
  let modBits = 1024 in
  let n = List.Tot.map u8_from_UInt8 [
    0xa5uy; 0x6euy; 0x4auy; 0x0euy; 0x70uy; 0x10uy; 0x17uy; 0x58uy; 0x9auy; 0x51uy; 0x87uy; 0xdcuy; 0x7euy; 0xa8uy; 0x41uy; 0xd1uy;
    0x56uy; 0xf2uy; 0xecuy; 0x0euy; 0x36uy; 0xaduy; 0x52uy; 0xa4uy; 0x4duy; 0xfeuy; 0xb1uy; 0xe6uy; 0x1fuy; 0x7auy; 0xd9uy; 0x91uy;
    0xd8uy; 0xc5uy; 0x10uy; 0x56uy; 0xffuy; 0xeduy; 0xb1uy; 0x62uy; 0xb4uy; 0xc0uy; 0xf2uy; 0x83uy; 0xa1uy; 0x2auy; 0x88uy; 0xa3uy;
    0x94uy; 0xdfuy; 0xf5uy; 0x26uy; 0xabuy; 0x72uy; 0x91uy; 0xcbuy; 0xb3uy; 0x07uy; 0xceuy; 0xabuy; 0xfcuy; 0xe0uy; 0xb1uy; 0xdfuy;
    0xd5uy; 0xcduy; 0x95uy; 0x08uy; 0x09uy; 0x6duy; 0x5buy; 0x2buy; 0x8buy; 0x6duy; 0xf5uy; 0xd6uy; 0x71uy; 0xefuy; 0x63uy; 0x77uy;
    0xc0uy; 0x92uy; 0x1cuy; 0xb2uy; 0x3cuy; 0x27uy; 0x0auy; 0x70uy; 0xe2uy; 0x59uy; 0x8euy; 0x6fuy; 0xf8uy; 0x9duy; 0x19uy; 0xf1uy;
    0x05uy; 0xacuy; 0xc2uy; 0xd3uy; 0xf0uy; 0xcbuy; 0x35uy; 0xf2uy; 0x92uy; 0x80uy; 0xe1uy; 0x38uy; 0x6buy; 0x6fuy; 0x64uy; 0xc4uy;
    0xefuy; 0x22uy; 0xe1uy; 0xe1uy; 0xf2uy; 0x0duy; 0x0cuy; 0xe8uy; 0xcfuy; 0xfbuy; 0x22uy; 0x49uy; 0xbduy; 0x9auy; 0x21uy; 0x37uy] in
  let n : lbytes 128 = createL n in
  let e = List.Tot.map u8_from_UInt8 [0x01uy; 0x00uy; 0x01uy] in
  let e : lbytes 3 = createL e in
  let d = List.Tot.map u8_from_UInt8 [
    0x33uy; 0xa5uy; 0x04uy; 0x2auy; 0x90uy; 0xb2uy; 0x7duy; 0x4fuy; 0x54uy; 0x51uy; 0xcauy; 0x9buy; 0xbbuy; 0xd0uy; 0xb4uy; 0x47uy;
    0x71uy; 0xa1uy; 0x01uy; 0xafuy; 0x88uy; 0x43uy; 0x40uy; 0xaeuy; 0xf9uy; 0x88uy; 0x5fuy; 0x2auy; 0x4buy; 0xbeuy; 0x92uy; 0xe8uy;
    0x94uy; 0xa7uy; 0x24uy; 0xacuy; 0x3cuy; 0x56uy; 0x8cuy; 0x8fuy; 0x97uy; 0x85uy; 0x3auy; 0xd0uy; 0x7cuy; 0x02uy; 0x66uy; 0xc8uy;
    0xc6uy; 0xa3uy; 0xcauy; 0x09uy; 0x29uy; 0xf1uy; 0xe8uy; 0xf1uy; 0x12uy; 0x31uy; 0x88uy; 0x44uy; 0x29uy; 0xfcuy; 0x4duy; 0x9auy;
    0xe5uy; 0x5fuy; 0xeeuy; 0x89uy; 0x6auy; 0x10uy; 0xceuy; 0x70uy; 0x7cuy; 0x3euy; 0xd7uy; 0xe7uy; 0x34uy; 0xe4uy; 0x47uy; 0x27uy;
    0xa3uy; 0x95uy; 0x74uy; 0x50uy; 0x1auy; 0x53uy; 0x26uy; 0x83uy; 0x10uy; 0x9cuy; 0x2auy; 0xbauy; 0xcauy; 0xbauy; 0x28uy; 0x3cuy;
    0x31uy; 0xb4uy; 0xbduy; 0x2fuy; 0x53uy; 0xc3uy; 0xeeuy; 0x37uy; 0xe3uy; 0x52uy; 0xceuy; 0xe3uy; 0x4fuy; 0x9euy; 0x50uy; 0x3buy;
    0xd8uy; 0x0cuy; 0x06uy; 0x22uy; 0xaduy; 0x79uy; 0xc6uy; 0xdcuy; 0xeeuy; 0x88uy; 0x35uy; 0x47uy; 0xc6uy; 0xa3uy; 0xb3uy; 0x25uy ] in
  let d : lbytes 128 = createL d in
  let p = List.Tot.map u8_from_UInt8 [
    0xe7uy; 0xe8uy; 0x94uy; 0x27uy; 0x20uy; 0xa8uy; 0x77uy; 0x51uy; 0x72uy; 0x73uy; 0xa3uy; 0x56uy; 0x05uy; 0x3euy; 0xa2uy; 0xa1uy;
    0xbcuy; 0x0cuy; 0x94uy; 0xaauy; 0x72uy; 0xd5uy; 0x5cuy; 0x6euy; 0x86uy; 0x29uy; 0x6buy; 0x2duy; 0xfcuy; 0x96uy; 0x79uy; 0x48uy;
    0xc0uy; 0xa7uy; 0x2cuy; 0xbcuy; 0xccuy; 0xa7uy; 0xeauy; 0xcbuy; 0x35uy; 0x70uy; 0x6euy; 0x09uy; 0xa1uy; 0xdfuy; 0x55uy; 0xa1uy;
    0x53uy; 0x5buy; 0xd9uy; 0xb3uy; 0xccuy; 0x34uy; 0x16uy; 0x0buy; 0x3buy; 0x6duy; 0xcduy; 0x3euy; 0xdauy; 0x8euy; 0x64uy; 0x43uy ] in
  let p : lbytes 64 = createL p in
  let q = List.Tot.map u8_from_UInt8 [
    0xb6uy; 0x9duy; 0xcauy; 0x1cuy; 0xf7uy; 0xd4uy; 0xd7uy; 0xecuy; 0x81uy; 0xe7uy; 0x5buy; 0x90uy; 0xfcuy; 0xcauy; 0x87uy; 0x4auy;
    0xbcuy; 0xdeuy; 0x12uy; 0x3fuy; 0xd2uy; 0x70uy; 0x01uy; 0x80uy; 0xaauy; 0x90uy; 0x47uy; 0x9buy; 0x6euy; 0x48uy; 0xdeuy; 0x8duy;
    0x67uy; 0xeduy; 0x24uy; 0xf9uy; 0xf1uy; 0x9duy; 0x85uy; 0xbauy; 0x27uy; 0x58uy; 0x74uy; 0xf5uy; 0x42uy; 0xcduy; 0x20uy; 0xdcuy;
    0x72uy; 0x3euy; 0x69uy; 0x63uy; 0x36uy; 0x4auy; 0x1fuy; 0x94uy; 0x25uy; 0x45uy; 0x2buy; 0x26uy; 0x9auy; 0x67uy; 0x99uy; 0xfduy ] in
  let q : lbytes 64 = createL q in
  let rBlind = List.Tot.map u8_from_UInt8 [0xa5uy; 0x6euy; 0x4auy; 0x0euy; 0x70uy; 0x10uy; 0x17uy; 0x58uy] in
  let rBlind : lbytes 8 = createL rBlind in

  let msg = List.Tot.map u8_from_UInt8 [
    0x85uy; 0x13uy; 0x84uy; 0xcduy; 0xfeuy; 0x81uy; 0x9cuy; 0x22uy; 0xeduy; 0x6cuy; 0x4cuy; 0xcbuy; 0x30uy; 0xdauy; 0xebuy; 0x5cuy;
    0xf0uy; 0x59uy; 0xbcuy; 0x8euy; 0x11uy; 0x66uy; 0xb7uy; 0xe3uy; 0x53uy; 0x0cuy; 0x4cuy; 0x23uy; 0x3euy; 0x2buy; 0x5fuy; 0x8fuy;
    0x71uy; 0xa1uy; 0xccuy; 0xa5uy; 0x82uy; 0xd4uy; 0x3euy; 0xccuy; 0x72uy; 0xb1uy; 0xbcuy; 0xa1uy; 0x6duy; 0xfcuy; 0x70uy; 0x13uy;
    0x22uy; 0x6buy; 0x9euy] in
  let msg : lbytes 51 = createL msg in
  let sgnt_expected = List.Tot.map u8_from_UInt8 [
    0x62uy; 0xebuy; 0xb8uy; 0x03uy; 0x3auy; 0x2duy; 0x0buy; 0x8buy; 0xecuy; 0x42uy; 0x56uy; 0x52uy; 0x29uy; 0x9buy; 0x3fuy; 0x02uy;
    0x8fuy; 0xa8uy; 0x0cuy; 0x28uy; 0x11uy; 0x0duy; 0xf5uy; 0x37uy; 0x47uy; 0x2euy; 0x5euy; 0xd6uy; 0x28uy; 0x62uy; 0xb9uy; 0x98uy;
    0x36uy; 0xe5uy; 0x7auy; 0xa9uy; 0x8duy; 0x4buy; 0x94uy; 0x9auy; 0x21uy; 0xf0uy; 0x21uy; 0xeeuy; 0x33uy; 0x89uy; 0xffuy; 0x52uy;
    0x66uy; 0xe0uy; 0x54uy; 0xd4uy; 0x4euy; 0x8cuy; 0x92uy; 0x48uy; 0x0auy; 0xc9uy; 0x10uy; 0x67uy; 0xdeuy; 0xfbuy; 0xaeuy; 0xd4uy;
    0xdcuy; 0x3cuy; 0xe2uy; 0x43uy; 0xe8uy; 0x17uy; 0x52uy; 0x66uy; 0xd3uy; 0xecuy; 0x69uy; 0xfduy; 0xb0uy; 0xeduy; 0xeauy; 0xc1uy;
    0x1cuy; 0x8cuy; 0x9euy; 0x3euy; 0x99uy; 0x41uy; 0x54uy; 0xa9uy; 0x33uy; 0x95uy; 0xa5uy; 0x11uy; 0xb4uy; 0xa1uy; 0x72uy; 0xf6uy;
    0x64uy; 0x4fuy; 0x37uy; 0xf6uy; 0x80uy; 0x7buy; 0x86uy; 0x71uy; 0x6fuy; 0xc9uy; 0x07uy; 0xe1uy; 0xd0uy; 0xfcuy; 0x75uy; 0xbduy;
    0xa7uy; 0x7euy; 0x41uy; 0x1buy; 0xfcuy; 0x60uy; 0xfduy; 0x2euy; 0xd9uy; 0x27uy; 0x8euy; 0x92uy; 0x1auy; 0x33uy; 0x02uy; 0x1fuy] in
  let sgnt_expected : lbytes 128 = createL sgnt_expected in
  let salt = List.Tot.map u8_from_UInt8 [
    0xefuy; 0x28uy; 0x69uy; 0xfauy; 0x40uy; 0xc3uy; 0x46uy; 0xcbuy; 0x18uy; 0x3duy; 0xabuy; 0x3duy; 0x7buy; 0xffuy; 0xc9uy; 0x8fuy;
    0xd5uy; 0x6duy; 0xf4uy; 0x2duy] in
  let salt : lbytes 20 = createL salt in
  let modBits2 = modBits / 2 in
  ctest modBits n 17 e modBits d modBits2 p modBits2 q 51 msg 20 salt rBlind sgnt_expected (1uy)


val test2: unit -> ML bool
let test2() =
  let modBits = 1025 in
  let n = List.Tot.map u8_from_UInt8 [
    0x01uy; 0xd4uy; 0x0cuy; 0x1buy; 0xcfuy; 0x97uy; 0xa6uy; 0x8auy; 0xe7uy; 0xcduy; 0xbduy; 0x8auy; 0x7buy; 0xf3uy; 0xe3uy; 0x4fuy;
    0xa1uy; 0x9duy; 0xccuy; 0xa4uy; 0xefuy; 0x75uy; 0xa4uy; 0x74uy; 0x54uy; 0x37uy; 0x5fuy; 0x94uy; 0x51uy; 0x4duy; 0x88uy; 0xfeuy;
    0xd0uy; 0x06uy; 0xfbuy; 0x82uy; 0x9fuy; 0x84uy; 0x19uy; 0xffuy; 0x87uy; 0xd6uy; 0x31uy; 0x5duy; 0xa6uy; 0x8auy; 0x1fuy; 0xf3uy;
    0xa0uy; 0x93uy; 0x8euy; 0x9auy; 0xbbuy; 0x34uy; 0x64uy; 0x01uy; 0x1cuy; 0x30uy; 0x3auy; 0xd9uy; 0x91uy; 0x99uy; 0xcfuy; 0x0cuy;
    0x7cuy; 0x7auy; 0x8buy; 0x47uy; 0x7duy; 0xceuy; 0x82uy; 0x9euy; 0x88uy; 0x44uy; 0xf6uy; 0x25uy; 0xb1uy; 0x15uy; 0xe5uy; 0xe9uy;
    0xc4uy; 0xa5uy; 0x9cuy; 0xf8uy; 0xf8uy; 0x11uy; 0x3buy; 0x68uy; 0x34uy; 0x33uy; 0x6auy; 0x2fuy; 0xd2uy; 0x68uy; 0x9buy; 0x47uy;
    0x2cuy; 0xbbuy; 0x5euy; 0x5cuy; 0xabuy; 0xe6uy; 0x74uy; 0x35uy; 0x0cuy; 0x59uy; 0xb6uy; 0xc1uy; 0x7euy; 0x17uy; 0x68uy; 0x74uy;
    0xfbuy; 0x42uy; 0xf8uy; 0xfcuy; 0x3duy; 0x17uy; 0x6auy; 0x01uy; 0x7euy; 0xdcuy; 0x61uy; 0xfduy; 0x32uy; 0x6cuy; 0x4buy; 0x33uy;
    0xc9uy ] in
  let n : lbytes 129 = createL n in
  let e = List.Tot.map u8_from_UInt8 [0x01uy; 0x00uy; 0x01uy] in
  let e : lbytes 3 = createL e in
  let d = List.Tot.map u8_from_UInt8 [
    0x02uy; 0x7duy; 0x14uy; 0x7euy; 0x46uy; 0x73uy; 0x05uy; 0x73uy; 0x77uy; 0xfduy; 0x1euy; 0xa2uy; 0x01uy; 0x56uy; 0x57uy; 0x72uy;
    0x17uy; 0x6auy; 0x7duy; 0xc3uy; 0x83uy; 0x58uy; 0xd3uy; 0x76uy; 0x04uy; 0x56uy; 0x85uy; 0xa2uy; 0xe7uy; 0x87uy; 0xc2uy; 0x3cuy;
    0x15uy; 0x57uy; 0x6buy; 0xc1uy; 0x6buy; 0x9fuy; 0x44uy; 0x44uy; 0x02uy; 0xd6uy; 0xbfuy; 0xc5uy; 0xd9uy; 0x8auy; 0x3euy; 0x88uy;
    0xeauy; 0x13uy; 0xefuy; 0x67uy; 0xc3uy; 0x53uy; 0xecuy; 0xa0uy; 0xc0uy; 0xdduy; 0xbauy; 0x92uy; 0x55uy; 0xbduy; 0x7buy; 0x8buy;
    0xb5uy; 0x0auy; 0x64uy; 0x4auy; 0xfduy; 0xfduy; 0x1duy; 0xd5uy; 0x16uy; 0x95uy; 0xb2uy; 0x52uy; 0xd2uy; 0x2euy; 0x73uy; 0x18uy;
    0xd1uy; 0xb6uy; 0x68uy; 0x7auy; 0x1cuy; 0x10uy; 0xffuy; 0x75uy; 0x54uy; 0x5fuy; 0x3duy; 0xb0uy; 0xfeuy; 0x60uy; 0x2duy; 0x5fuy;
    0x2buy; 0x7fuy; 0x29uy; 0x4euy; 0x36uy; 0x01uy; 0xeauy; 0xb7uy; 0xb9uy; 0xd1uy; 0xceuy; 0xcduy; 0x76uy; 0x7fuy; 0x64uy; 0x69uy;
    0x2euy; 0x3euy; 0x53uy; 0x6cuy; 0xa2uy; 0x84uy; 0x6cuy; 0xb0uy; 0xc2uy; 0xdduy; 0x48uy; 0x6auy; 0x39uy; 0xfauy; 0x75uy; 0xb1uy ] in
  let d : lbytes 128 = createL d in
  let p = List.Tot.map u8_from_UInt8 [
    0x01uy; 0x66uy; 0x01uy; 0xe9uy; 0x26uy; 0xa0uy; 0xf8uy; 0xc9uy; 0xe2uy; 0x6euy; 0xcauy; 0xb7uy; 0x69uy; 0xeauy; 0x65uy; 0xa5uy;
    0xe7uy; 0xc5uy; 0x2cuy; 0xc9uy; 0xe0uy; 0x80uy; 0xefuy; 0x51uy; 0x94uy; 0x57uy; 0xc6uy; 0x44uy; 0xdauy; 0x68uy; 0x91uy; 0xc5uy;
    0xa1uy; 0x04uy; 0xd3uy; 0xeauy; 0x79uy; 0x55uy; 0x92uy; 0x9auy; 0x22uy; 0xe7uy; 0xc6uy; 0x8auy; 0x7auy; 0xf9uy; 0xfcuy; 0xaduy;
    0x77uy; 0x7cuy; 0x3cuy; 0xccuy; 0x2buy; 0x9euy; 0x3duy; 0x36uy; 0x50uy; 0xbcuy; 0xe4uy; 0x04uy; 0x39uy; 0x9buy; 0x7euy; 0x59uy;
    0xd1uy ] in
  let p : lbytes 65 = createL p in
  let q = List.Tot.map u8_from_UInt8 [
    0x01uy; 0x4euy; 0xafuy; 0xa1uy; 0xd4uy; 0xd0uy; 0x18uy; 0x4duy; 0xa7uy; 0xe3uy; 0x1fuy; 0x87uy; 0x7duy; 0x12uy; 0x81uy; 0xdduy;
    0xdauy; 0x62uy; 0x56uy; 0x64uy; 0x86uy; 0x9euy; 0x83uy; 0x79uy; 0xe6uy; 0x7auy; 0xd3uy; 0xb7uy; 0x5euy; 0xaeuy; 0x74uy; 0xa5uy;
    0x80uy; 0xe9uy; 0x82uy; 0x7auy; 0xbduy; 0x6euy; 0xb7uy; 0xa0uy; 0x02uy; 0xcbuy; 0x54uy; 0x11uy; 0xf5uy; 0x26uy; 0x67uy; 0x97uy;
    0x76uy; 0x8fuy; 0xb8uy; 0xe9uy; 0x5auy; 0xe4uy; 0x0euy; 0x3euy; 0x8auy; 0x01uy; 0xf3uy; 0x5fuy; 0xf8uy; 0x9euy; 0x56uy; 0xc0uy;
    0x79uy ] in
  let q : lbytes 65 = createL q in
  let rBlind = List.Tot.map u8_from_UInt8 [0xbbuy; 0x34uy; 0x64uy; 0x01uy; 0x1cuy; 0x30uy; 0x3auy; 0xd9uy] in
  let rBlind : lbytes 8 = createL rBlind in

  let msg = List.Tot.map u8_from_UInt8 [
    0xe4uy; 0xf8uy; 0x60uy; 0x1auy; 0x8auy; 0x6duy; 0xa1uy; 0xbeuy; 0x34uy; 0x44uy; 0x7cuy; 0x09uy; 0x59uy; 0xc0uy; 0x58uy; 0x57uy;
    0x0cuy; 0x36uy; 0x68uy; 0xcfuy; 0xd5uy; 0x1duy; 0xd5uy; 0xf9uy; 0xccuy; 0xd6uy; 0xaduy; 0x44uy; 0x11uy; 0xfeuy; 0x82uy; 0x13uy;
    0x48uy; 0x6duy; 0x78uy; 0xa6uy; 0xc4uy; 0x9fuy; 0x93uy; 0xefuy; 0xc2uy; 0xcauy; 0x22uy; 0x88uy; 0xceuy; 0xbcuy; 0x2buy; 0x9buy;
    0x60uy; 0xbduy; 0x04uy; 0xb1uy; 0xe2uy; 0x20uy; 0xd8uy; 0x6euy; 0x3duy; 0x48uy; 0x48uy; 0xd7uy; 0x09uy; 0xd0uy; 0x32uy; 0xd1uy;
    0xe8uy; 0xc6uy; 0xa0uy; 0x70uy; 0xc6uy; 0xafuy; 0x9auy; 0x49uy; 0x9fuy; 0xcfuy; 0x95uy; 0x35uy; 0x4buy; 0x14uy; 0xbauy; 0x61uy;
    0x27uy; 0xc7uy; 0x39uy; 0xdeuy; 0x1buy; 0xb0uy; 0xfduy; 0x16uy; 0x43uy; 0x1euy; 0x46uy; 0x93uy; 0x8auy; 0xecuy; 0x0cuy; 0xf8uy;
    0xaduy; 0x9euy; 0xb7uy; 0x2euy; 0x83uy; 0x2auy; 0x70uy; 0x35uy; 0xdeuy; 0x9buy; 0x78uy; 0x07uy; 0xbduy; 0xc0uy; 0xeduy; 0x8buy;
    0x68uy; 0xebuy; 0x0fuy; 0x5auy; 0xc2uy; 0x21uy; 0x6buy; 0xe4uy; 0x0cuy; 0xe9uy; 0x20uy; 0xc0uy; 0xdbuy; 0x0euy; 0xdduy; 0xd3uy;
    0x86uy; 0x0euy; 0xd7uy; 0x88uy; 0xefuy; 0xacuy; 0xcauy; 0xcauy; 0x50uy; 0x2duy; 0x8fuy; 0x2buy; 0xd6uy; 0xd1uy; 0xa7uy; 0xc1uy;
    0xf4uy; 0x1fuy; 0xf4uy; 0x6fuy; 0x16uy; 0x81uy; 0xc8uy; 0xf1uy; 0xf8uy; 0x18uy; 0xe9uy; 0xc4uy; 0xf6uy; 0xd9uy; 0x1auy; 0x0cuy;
    0x78uy; 0x03uy; 0xccuy; 0xc6uy; 0x3duy; 0x76uy; 0xa6uy; 0x54uy; 0x4duy; 0x84uy; 0x3euy; 0x08uy; 0x4euy; 0x36uy; 0x3buy; 0x8auy;
    0xccuy; 0x55uy; 0xaauy; 0x53uy; 0x17uy; 0x33uy; 0xeduy; 0xb5uy; 0xdeuy; 0xe5uy; 0xb5uy; 0x19uy; 0x6euy; 0x9fuy; 0x03uy; 0xe8uy;
    0xb7uy; 0x31uy; 0xb3uy; 0x77uy; 0x64uy; 0x28uy; 0xd9uy; 0xe4uy; 0x57uy; 0xfeuy; 0x3fuy; 0xbcuy; 0xb3uy; 0xdbuy; 0x72uy; 0x74uy;
    0x44uy; 0x2duy; 0x78uy; 0x58uy; 0x90uy; 0xe9uy; 0xcbuy; 0x08uy; 0x54uy; 0xb6uy; 0x44uy; 0x4duy; 0xacuy; 0xe7uy; 0x91uy; 0xd7uy;
    0x27uy; 0x3duy; 0xe1uy; 0x88uy; 0x97uy; 0x19uy; 0x33uy; 0x8auy; 0x77uy; 0xfeuy ] in
  let msg: lbytes 234 = createL msg in
  let salt = List.Tot.map u8_from_UInt8 [
    0x7fuy; 0x6duy; 0xd3uy; 0x59uy; 0xe6uy; 0x04uy; 0xe6uy; 0x08uy; 0x70uy; 0xe8uy; 0x98uy; 0xe4uy; 0x7buy; 0x19uy; 0xbfuy; 0x2euy;
    0x5auy; 0x7buy; 0x2auy; 0x90uy ] in
  let salt : lbytes 20 = createL salt in
  let sgnt_expected = List.Tot.map u8_from_UInt8 [
    0x01uy; 0x90uy; 0x44uy; 0x7auy; 0x91uy; 0xa3uy; 0xefuy; 0x1euy; 0x9auy; 0x36uy; 0x44uy; 0xb2uy; 0x2duy; 0xb0uy; 0x9duy; 0xb3uy;
    0x7buy; 0x45uy; 0xe1uy; 0xd5uy; 0xfauy; 0x2euy; 0xa0uy; 0x8auy; 0xecuy; 0x35uy; 0xd9uy; 0x81uy; 0x54uy; 0xc5uy; 0x2fuy; 0x31uy;
    0x5duy; 0x4auy; 0x71uy; 0x26uy; 0x70uy; 0xa2uy; 0x7euy; 0xc4uy; 0xe5uy; 0xe3uy; 0xa0uy; 0x96uy; 0xf2uy; 0xe1uy; 0x0auy; 0xa6uy;
    0x23uy; 0x90uy; 0x66uy; 0x40uy; 0x42uy; 0xc7uy; 0xb6uy; 0xb8uy; 0x2fuy; 0x24uy; 0x79uy; 0x70uy; 0xc6uy; 0x74uy; 0xf0uy; 0xcauy;
    0x79uy; 0x57uy; 0xb9uy; 0xe0uy; 0xf3uy; 0x0buy; 0x23uy; 0x39uy; 0x07uy; 0x71uy; 0xeeuy; 0x4auy; 0x67uy; 0xd9uy; 0x1buy; 0x30uy;
    0x39uy; 0xc6uy; 0x45uy; 0xeeuy; 0x63uy; 0x7fuy; 0x50uy; 0x84uy; 0x20uy; 0x2duy; 0x5buy; 0x03uy; 0x03uy; 0xd5uy; 0x46uy; 0x6duy;
    0x92uy; 0x72uy; 0xc5uy; 0xd7uy; 0x73uy; 0x36uy; 0x8auy; 0xbcuy; 0x06uy; 0x84uy; 0xd6uy; 0xbcuy; 0xc1uy; 0x9duy; 0x30uy; 0x27uy;
    0x73uy; 0x24uy; 0x54uy; 0x3euy; 0xcduy; 0xafuy; 0x56uy; 0xf7uy; 0x44uy; 0x6euy; 0x20uy; 0x79uy; 0xb8uy; 0x9cuy; 0xc4uy; 0x8fuy;
    0x2duy ] in
  let sgnt_expected : lbytes 129 = createL sgnt_expected in
  ctest modBits n 17 e 1024 d (65*8) p (65*8) q 234 msg 20 salt rBlind sgnt_expected (2uy)


val test3: unit -> ML bool
let test3() =
  let modBits = 1536 in
  let n = List.Tot.map u8_from_UInt8 [
    0xe6uy; 0xbduy; 0x69uy; 0x2auy; 0xc9uy; 0x66uy; 0x45uy; 0x79uy; 0x04uy; 0x03uy; 0xfduy; 0xd0uy; 0xf5uy; 0xbeuy; 0xb8uy; 0xb9uy;
    0xbfuy; 0x92uy; 0xeduy; 0x10uy; 0x00uy; 0x7fuy; 0xc3uy; 0x65uy; 0x04uy; 0x64uy; 0x19uy; 0xdduy; 0x06uy; 0xc0uy; 0x5cuy; 0x5buy;
    0x5buy; 0x2fuy; 0x48uy; 0xecuy; 0xf9uy; 0x89uy; 0xe4uy; 0xceuy; 0x26uy; 0x91uy; 0x09uy; 0x97uy; 0x9cuy; 0xbbuy; 0x40uy; 0xb4uy;
    0xa0uy; 0xaduy; 0x24uy; 0xd2uy; 0x24uy; 0x83uy; 0xd1uy; 0xeeuy; 0x31uy; 0x5auy; 0xd4uy; 0xccuy; 0xb1uy; 0x53uy; 0x42uy; 0x68uy;
    0x35uy; 0x26uy; 0x91uy; 0xc5uy; 0x24uy; 0xf6uy; 0xdduy; 0x8euy; 0x6cuy; 0x29uy; 0xd2uy; 0x24uy; 0xcfuy; 0x24uy; 0x69uy; 0x73uy;
    0xaeuy; 0xc8uy; 0x6cuy; 0x5buy; 0xf6uy; 0xb1uy; 0x40uy; 0x1auy; 0x85uy; 0x0duy; 0x1buy; 0x9auy; 0xd1uy; 0xbbuy; 0x8cuy; 0xbcuy;
    0xecuy; 0x47uy; 0xb0uy; 0x6fuy; 0x0fuy; 0x8cuy; 0x7fuy; 0x45uy; 0xd3uy; 0xfcuy; 0x8fuy; 0x31uy; 0x92uy; 0x99uy; 0xc5uy; 0x43uy;
    0x3duy; 0xdbuy; 0xc2uy; 0xb3uy; 0x05uy; 0x3buy; 0x47uy; 0xdeuy; 0xd2uy; 0xecuy; 0xd4uy; 0xa4uy; 0xcauy; 0xefuy; 0xd6uy; 0x14uy;
    0x83uy; 0x3duy; 0xc8uy; 0xbbuy; 0x62uy; 0x2fuy; 0x31uy; 0x7euy; 0xd0uy; 0x76uy; 0xb8uy; 0x05uy; 0x7fuy; 0xe8uy; 0xdeuy; 0x3fuy;
    0x84uy; 0x48uy; 0x0auy; 0xd5uy; 0xe8uy; 0x3euy; 0x4auy; 0x61uy; 0x90uy; 0x4auy; 0x4fuy; 0x24uy; 0x8fuy; 0xb3uy; 0x97uy; 0x02uy;
    0x73uy; 0x57uy; 0xe1uy; 0xd3uy; 0x0euy; 0x46uy; 0x31uy; 0x39uy; 0x81uy; 0x5cuy; 0x6fuy; 0xd4uy; 0xfduy; 0x5auy; 0xc5uy; 0xb8uy;
    0x17uy; 0x2auy; 0x45uy; 0x23uy; 0x0euy; 0xcbuy; 0x63uy; 0x18uy; 0xa0uy; 0x4fuy; 0x14uy; 0x55uy; 0xd8uy; 0x4euy; 0x5auy; 0x8buy] in
  let n : lbytes 192 = createL n in
  let e = List.Tot.map u8_from_UInt8 [0x01uy; 0x00uy; 0x01uy] in
  let e : lbytes 3 = createL e in
  let d = List.Tot.map u8_from_UInt8 [
    0x6auy; 0x7fuy; 0xd8uy; 0x4fuy; 0xb8uy; 0x5fuy; 0xaduy; 0x07uy; 0x3buy; 0x34uy; 0x40uy; 0x6duy; 0xb7uy; 0x4fuy; 0x8duy; 0x61uy;
    0xa6uy; 0xabuy; 0xc1uy; 0x21uy; 0x96uy; 0xa9uy; 0x61uy; 0xdduy; 0x79uy; 0x56uy; 0x5euy; 0x9duy; 0xa6uy; 0xe5uy; 0x18uy; 0x7buy;
    0xceuy; 0x2duy; 0x98uy; 0x02uy; 0x50uy; 0xf7uy; 0x35uy; 0x95uy; 0x75uy; 0x35uy; 0x92uy; 0x70uy; 0xd9uy; 0x15uy; 0x90uy; 0xbbuy;
    0x0euy; 0x42uy; 0x7cuy; 0x71uy; 0x46uy; 0x0buy; 0x55uy; 0xd5uy; 0x14uy; 0x10uy; 0xb1uy; 0x91uy; 0xbcuy; 0xf3uy; 0x09uy; 0xfeuy;
    0xa1uy; 0x31uy; 0xa9uy; 0x2cuy; 0x8euy; 0x70uy; 0x27uy; 0x38uy; 0xfauy; 0x71uy; 0x9fuy; 0x1euy; 0x00uy; 0x41uy; 0xf5uy; 0x2euy;
    0x40uy; 0xe9uy; 0x1fuy; 0x22uy; 0x9fuy; 0x4duy; 0x96uy; 0xa1uy; 0xe6uy; 0xf1uy; 0x72uy; 0xe1uy; 0x55uy; 0x96uy; 0xb4uy; 0x51uy;
    0x0auy; 0x6duy; 0xaeuy; 0xc2uy; 0x61uy; 0x05uy; 0xf2uy; 0xbeuy; 0xbcuy; 0x53uy; 0x31uy; 0x6buy; 0x87uy; 0xbduy; 0xf2uy; 0x13uy;
    0x11uy; 0x66uy; 0x60uy; 0x70uy; 0xe8uy; 0xdfuy; 0xeeuy; 0x69uy; 0xd5uy; 0x2cuy; 0x71uy; 0xa9uy; 0x76uy; 0xcauy; 0xaeuy; 0x79uy;
    0xc7uy; 0x2buy; 0x68uy; 0xd2uy; 0x85uy; 0x80uy; 0xdcuy; 0x68uy; 0x6duy; 0x9fuy; 0x51uy; 0x29uy; 0xd2uy; 0x25uy; 0xf8uy; 0x2buy;
    0x3duy; 0x61uy; 0x55uy; 0x13uy; 0xa8uy; 0x82uy; 0xb3uy; 0xdbuy; 0x91uy; 0x41uy; 0x6buy; 0x48uy; 0xceuy; 0x08uy; 0x88uy; 0x82uy;
    0x13uy; 0xe3uy; 0x7euy; 0xebuy; 0x9auy; 0xf8uy; 0x00uy; 0xd8uy; 0x1cuy; 0xabuy; 0x32uy; 0x8cuy; 0xe4uy; 0x20uy; 0x68uy; 0x99uy;
    0x03uy; 0xc0uy; 0x0cuy; 0x7buy; 0x5fuy; 0xd3uy; 0x1buy; 0x75uy; 0x50uy; 0x3auy; 0x6duy; 0x41uy; 0x96uy; 0x84uy; 0xd6uy; 0x29uy ] in
  let d : lbytes 192 = createL d in
  let p = List.Tot.map u8_from_UInt8 [
    0xf8uy; 0xebuy; 0x97uy; 0xe9uy; 0x8duy; 0xf1uy; 0x26uy; 0x64uy; 0xeeuy; 0xfduy; 0xb7uy; 0x61uy; 0x59uy; 0x6auy; 0x69uy; 0xdduy;
    0xcduy; 0x0euy; 0x76uy; 0xdauy; 0xecuy; 0xe6uy; 0xeduy; 0x4buy; 0xf5uy; 0xa1uy; 0xb5uy; 0x0auy; 0xc0uy; 0x86uy; 0xf7uy; 0x92uy;
    0x8auy; 0x4duy; 0x2fuy; 0x87uy; 0x26uy; 0xa7uy; 0x7euy; 0x51uy; 0x5buy; 0x74uy; 0xdauy; 0x41uy; 0x98uy; 0x8fuy; 0x22uy; 0x0buy;
    0x1cuy; 0xc8uy; 0x7auy; 0xa1uy; 0xfcuy; 0x81uy; 0x0cuy; 0xe9uy; 0x9auy; 0x82uy; 0xf2uy; 0xd1uy; 0xceuy; 0x82uy; 0x1euy; 0xdcuy;
    0xeduy; 0x79uy; 0x4cuy; 0x69uy; 0x41uy; 0xf4uy; 0x2cuy; 0x7auy; 0x1auy; 0x0buy; 0x8cuy; 0x4duy; 0x28uy; 0xc7uy; 0x5euy; 0xc6uy;
    0x0buy; 0x65uy; 0x22uy; 0x79uy; 0xf6uy; 0x15uy; 0x4auy; 0x76uy; 0x2auy; 0xeduy; 0x16uy; 0x5duy; 0x47uy; 0xdeuy; 0xe3uy; 0x67uy ] in
  let p : lbytes 96 = createL p in
  let q = List.Tot.map u8_from_UInt8 [
    0xeduy; 0x4duy; 0x71uy; 0xd0uy; 0xa6uy; 0xe2uy; 0x4buy; 0x93uy; 0xc2uy; 0xe5uy; 0xf6uy; 0xb4uy; 0xbbuy; 0xe0uy; 0x5fuy; 0x5fuy;
    0xb0uy; 0xafuy; 0xa0uy; 0x42uy; 0xd2uy; 0x04uy; 0xfeuy; 0x33uy; 0x78uy; 0xd3uy; 0x65uy; 0xc2uy; 0xf2uy; 0x88uy; 0xb6uy; 0xa8uy;
    0xdauy; 0xd7uy; 0xefuy; 0xe4uy; 0x5duy; 0x15uy; 0x3euy; 0xefuy; 0x40uy; 0xcauy; 0xccuy; 0x7buy; 0x81uy; 0xffuy; 0x93uy; 0x40uy;
    0x02uy; 0xd1uy; 0x08uy; 0x99uy; 0x4buy; 0x94uy; 0xa5uy; 0xe4uy; 0x72uy; 0x8cuy; 0xd9uy; 0xc9uy; 0x63uy; 0x37uy; 0x5auy; 0xe4uy;
    0x99uy; 0x65uy; 0xbduy; 0xa5uy; 0x5cuy; 0xbfuy; 0x0euy; 0xfeuy; 0xd8uy; 0xd6uy; 0x55uy; 0x3buy; 0x40uy; 0x27uy; 0xf2uy; 0xd8uy;
    0x62uy; 0x08uy; 0xa6uy; 0xe6uy; 0xb4uy; 0x89uy; 0xc1uy; 0x76uy; 0x12uy; 0x80uy; 0x92uy; 0xd6uy; 0x29uy; 0xe4uy; 0x9duy; 0x3duy ] in
  let q :lbytes 96 = createL q in
  let rBlind = List.Tot.map u8_from_UInt8 [0x35uy; 0x26uy; 0x91uy; 0xc5uy; 0x24uy; 0xf6uy; 0xdduy; 0x8euy] in
  let rBlind : lbytes 8 = createL rBlind in

  let msg = List.Tot.map u8_from_UInt8 [
    0xc8uy; 0xc9uy; 0xc6uy; 0xafuy; 0x04uy; 0xacuy; 0xdauy; 0x41uy; 0x4duy; 0x22uy; 0x7euy; 0xf2uy; 0x3euy; 0x08uy; 0x20uy; 0xc3uy;
    0x73uy; 0x2cuy; 0x50uy; 0x0duy; 0xc8uy; 0x72uy; 0x75uy; 0xe9uy; 0x5buy; 0x0duy; 0x09uy; 0x54uy; 0x13uy; 0x99uy; 0x3cuy; 0x26uy;
    0x58uy; 0xbcuy; 0x1duy; 0x98uy; 0x85uy; 0x81uy; 0xbauy; 0x87uy; 0x9cuy; 0x2duy; 0x20uy; 0x1fuy; 0x14uy; 0xcbuy; 0x88uy; 0xceuy;
    0xd1uy; 0x53uy; 0xa0uy; 0x19uy; 0x69uy; 0xa7uy; 0xbfuy; 0x0auy; 0x7buy; 0xe7uy; 0x9cuy; 0x84uy; 0xc1uy; 0x48uy; 0x6buy; 0xc1uy;
    0x2buy; 0x3fuy; 0xa6uy; 0xc5uy; 0x98uy; 0x71uy; 0xb6uy; 0x82uy; 0x7cuy; 0x8cuy; 0xe2uy; 0x53uy; 0xcauy; 0x5fuy; 0xefuy; 0xa8uy;
    0xa8uy; 0xc6uy; 0x90uy; 0xbfuy; 0x32uy; 0x6euy; 0x8euy; 0x37uy; 0xcduy; 0xb9uy; 0x6duy; 0x90uy; 0xa8uy; 0x2euy; 0xbauy; 0xb6uy;
    0x9fuy; 0x86uy; 0x35uy; 0x0euy; 0x18uy; 0x22uy; 0xe8uy; 0xbduy; 0x53uy; 0x6auy; 0x2euy ] in
  let msg : lbytes 107 = createL msg in
  let salt = List.Tot.map u8_from_UInt8 [
    0xb3uy; 0x07uy; 0xc4uy; 0x3buy; 0x48uy; 0x50uy; 0xa8uy; 0xdauy; 0xc2uy; 0xf1uy; 0x5fuy; 0x32uy; 0xe3uy; 0x78uy; 0x39uy; 0xefuy;
    0x8cuy; 0x5cuy; 0x0euy; 0x91uy] in
  let salt : lbytes 20 = createL salt in
  let sgnt_expected = List.Tot.map u8_from_UInt8 [
    0x0cuy; 0x58uy; 0xaauy; 0x0auy; 0x5duy; 0xe6uy; 0xd8uy; 0xa0uy; 0x0buy; 0xb6uy; 0xacuy; 0x2duy; 0x5cuy; 0x04uy; 0xfbuy; 0x0fuy;
    0xa3uy; 0x01uy; 0x12uy; 0x49uy; 0x3buy; 0xdeuy; 0x42uy; 0x28uy; 0x8auy; 0x5buy; 0xaduy; 0x5cuy; 0x7buy; 0x4buy; 0x51uy; 0x8euy;
    0x21uy; 0xf3uy; 0x1cuy; 0x18uy; 0x54uy; 0x71uy; 0xb5uy; 0x9fuy; 0x87uy; 0x33uy; 0xc1uy; 0x3fuy; 0xe4uy; 0xc7uy; 0xfeuy; 0xc4uy;
    0xa2uy; 0x4duy; 0x0duy; 0x0cuy; 0xd6uy; 0x62uy; 0xecuy; 0xd5uy; 0xe7uy; 0x21uy; 0xb0uy; 0x53uy; 0x62uy; 0xd9uy; 0xb6uy; 0x72uy;
    0xa3uy; 0xd8uy; 0x26uy; 0x82uy; 0x55uy; 0x2cuy; 0x58uy; 0x30uy; 0x0duy; 0xa6uy; 0x14uy; 0x65uy; 0x66uy; 0x38uy; 0xe6uy; 0x61uy;
    0x83uy; 0x9duy; 0x33uy; 0xb4uy; 0xd3uy; 0xd3uy; 0x7euy; 0x0fuy; 0xceuy; 0x8buy; 0xa0uy; 0xe4uy; 0x93uy; 0xd0uy; 0x2buy; 0xc4uy;
    0x73uy; 0xf8uy; 0x53uy; 0x78uy; 0x71uy; 0xbbuy; 0x56uy; 0x55uy; 0xc6uy; 0x94uy; 0x07uy; 0xb3uy; 0x62uy; 0xe0uy; 0x73uy; 0x90uy;
    0x07uy; 0xe0uy; 0x36uy; 0x7auy; 0x39uy; 0xc0uy; 0x38uy; 0xceuy; 0xd3uy; 0x7fuy; 0xf4uy; 0xfbuy; 0x9fuy; 0x16uy; 0x0duy; 0x4duy;
    0x06uy; 0x39uy; 0x62uy; 0x17uy; 0x31uy; 0x5euy; 0xe8uy; 0xd7uy; 0x5duy; 0x91uy; 0x0buy; 0x51uy; 0x28uy; 0x45uy; 0xf9uy; 0x70uy;
    0xfeuy; 0x74uy; 0xe4uy; 0x12uy; 0x26uy; 0x84uy; 0x71uy; 0xc9uy; 0x51uy; 0x81uy; 0x62uy; 0x51uy; 0x6cuy; 0xd6uy; 0xf9uy; 0x66uy;
    0x89uy; 0x2auy; 0x74uy; 0x0euy; 0x1buy; 0x8auy; 0x88uy; 0x76uy; 0x6auy; 0x30uy; 0xfcuy; 0xe9uy; 0xb6uy; 0x0euy; 0x03uy; 0x32uy;
    0xd7uy; 0xa0uy; 0x1buy; 0xa5uy; 0xfauy; 0x13uy; 0x5fuy; 0xe7uy; 0xc4uy; 0x92uy; 0x72uy; 0xacuy; 0xbbuy; 0x1duy; 0x30uy; 0xf1uy] in
  let sgnt_expected : lbytes 192 = createL sgnt_expected in
  ctest modBits n 17 e modBits d (96*8) p (96*8) q 107 msg 20 salt rBlind sgnt_expected (3uy)


val test4: unit -> ML bool
let test4() =
  let modBits = 2048 in
  let n = List.Tot.map u8_from_UInt8 [
    0xa5uy; 0xdduy; 0x86uy; 0x7auy; 0xc4uy; 0xcbuy; 0x02uy; 0xf9uy; 0x0buy; 0x94uy; 0x57uy; 0xd4uy; 0x8cuy; 0x14uy; 0xa7uy; 0x70uy;
    0xefuy; 0x99uy; 0x1cuy; 0x56uy; 0xc3uy; 0x9cuy; 0x0euy; 0xc6uy; 0x5fuy; 0xd1uy; 0x1auy; 0xfauy; 0x89uy; 0x37uy; 0xceuy; 0xa5uy;
    0x7buy; 0x9buy; 0xe7uy; 0xacuy; 0x73uy; 0xb4uy; 0x5cuy; 0x00uy; 0x17uy; 0x61uy; 0x5buy; 0x82uy; 0xd6uy; 0x22uy; 0xe3uy; 0x18uy;
    0x75uy; 0x3buy; 0x60uy; 0x27uy; 0xc0uy; 0xfduy; 0x15uy; 0x7buy; 0xe1uy; 0x2fuy; 0x80uy; 0x90uy; 0xfeuy; 0xe2uy; 0xa7uy; 0xaduy;
    0xcduy; 0x0euy; 0xefuy; 0x75uy; 0x9fuy; 0x88uy; 0xbauy; 0x49uy; 0x97uy; 0xc7uy; 0xa4uy; 0x2duy; 0x58uy; 0xc9uy; 0xaauy; 0x12uy;
    0xcbuy; 0x99uy; 0xaeuy; 0x00uy; 0x1fuy; 0xe5uy; 0x21uy; 0xc1uy; 0x3buy; 0xb5uy; 0x43uy; 0x14uy; 0x45uy; 0xa8uy; 0xd5uy; 0xaeuy;
    0x4fuy; 0x5euy; 0x4cuy; 0x7euy; 0x94uy; 0x8auy; 0xc2uy; 0x27uy; 0xd3uy; 0x60uy; 0x40uy; 0x71uy; 0xf2uy; 0x0euy; 0x57uy; 0x7euy;
    0x90uy; 0x5fuy; 0xbeuy; 0xb1uy; 0x5duy; 0xfauy; 0xf0uy; 0x6duy; 0x1duy; 0xe5uy; 0xaeuy; 0x62uy; 0x53uy; 0xd6uy; 0x3auy; 0x6auy;
    0x21uy; 0x20uy; 0xb3uy; 0x1auy; 0x5duy; 0xa5uy; 0xdauy; 0xbcuy; 0x95uy; 0x50uy; 0x60uy; 0x0euy; 0x20uy; 0xf2uy; 0x7duy; 0x37uy;
    0x39uy; 0xe2uy; 0x62uy; 0x79uy; 0x25uy; 0xfeuy; 0xa3uy; 0xccuy; 0x50uy; 0x9fuy; 0x21uy; 0xdfuy; 0xf0uy; 0x4euy; 0x6euy; 0xeauy;
    0x45uy; 0x49uy; 0xc5uy; 0x40uy; 0xd6uy; 0x80uy; 0x9fuy; 0xf9uy; 0x30uy; 0x7euy; 0xeduy; 0xe9uy; 0x1fuy; 0xffuy; 0x58uy; 0x73uy;
    0x3duy; 0x83uy; 0x85uy; 0xa2uy; 0x37uy; 0xd6uy; 0xd3uy; 0x70uy; 0x5auy; 0x33uy; 0xe3uy; 0x91uy; 0x90uy; 0x09uy; 0x92uy; 0x07uy;
    0x0duy; 0xf7uy; 0xaduy; 0xf1uy; 0x35uy; 0x7cuy; 0xf7uy; 0xe3uy; 0x70uy; 0x0cuy; 0xe3uy; 0x66uy; 0x7duy; 0xe8uy; 0x3fuy; 0x17uy;
    0xb8uy; 0xdfuy; 0x17uy; 0x78uy; 0xdbuy; 0x38uy; 0x1duy; 0xceuy; 0x09uy; 0xcbuy; 0x4auy; 0xd0uy; 0x58uy; 0xa5uy; 0x11uy; 0x00uy;
    0x1auy; 0x73uy; 0x81uy; 0x98uy; 0xeeuy; 0x27uy; 0xcfuy; 0x55uy; 0xa1uy; 0x3buy; 0x75uy; 0x45uy; 0x39uy; 0x90uy; 0x65uy; 0x82uy;
    0xecuy; 0x8buy; 0x17uy; 0x4buy; 0xd5uy; 0x8duy; 0x5duy; 0x1fuy; 0x3duy; 0x76uy; 0x7cuy; 0x61uy; 0x37uy; 0x21uy; 0xaeuy; 0x05uy] in
  let n : lbytes 256 = createL n in
  let e = List.Tot.map u8_from_UInt8 [0x01uy; 0x00uy; 0x01uy] in
  let e : lbytes 3 = createL e in
  let d = List.Tot.map u8_from_UInt8 [
    0x2duy; 0x2fuy; 0xf5uy; 0x67uy; 0xb3uy; 0xfeuy; 0x74uy; 0xe0uy; 0x61uy; 0x91uy; 0xb7uy; 0xfduy; 0xeduy; 0x6duy; 0xe1uy; 0x12uy;
    0x29uy; 0x0cuy; 0x67uy; 0x06uy; 0x92uy; 0x43uy; 0x0duy; 0x59uy; 0x69uy; 0x18uy; 0x40uy; 0x47uy; 0xdauy; 0x23uy; 0x4cuy; 0x96uy;
    0x93uy; 0xdeuy; 0xeduy; 0x16uy; 0x73uy; 0xeduy; 0x42uy; 0x95uy; 0x39uy; 0xc9uy; 0x69uy; 0xd3uy; 0x72uy; 0xc0uy; 0x4duy; 0x6buy;
    0x47uy; 0xe0uy; 0xf5uy; 0xb8uy; 0xceuy; 0xe0uy; 0x84uy; 0x3euy; 0x5cuy; 0x22uy; 0x83uy; 0x5duy; 0xbduy; 0x3buy; 0x05uy; 0xa0uy;
    0x99uy; 0x79uy; 0x84uy; 0xaeuy; 0x60uy; 0x58uy; 0xb1uy; 0x1buy; 0xc4uy; 0x90uy; 0x7cuy; 0xbfuy; 0x67uy; 0xeduy; 0x84uy; 0xfauy;
    0x9auy; 0xe2uy; 0x52uy; 0xdfuy; 0xb0uy; 0xd0uy; 0xcduy; 0x49uy; 0xe6uy; 0x18uy; 0xe3uy; 0x5duy; 0xfduy; 0xfeuy; 0x59uy; 0xbcuy;
    0xa3uy; 0xdduy; 0xd6uy; 0x6cuy; 0x33uy; 0xceuy; 0xbbuy; 0xc7uy; 0x7auy; 0xd4uy; 0x41uy; 0xaauy; 0x69uy; 0x5euy; 0x13uy; 0xe3uy;
    0x24uy; 0xb5uy; 0x18uy; 0xf0uy; 0x1cuy; 0x60uy; 0xf5uy; 0xa8uy; 0x5cuy; 0x99uy; 0x4auy; 0xd1uy; 0x79uy; 0xf2uy; 0xa6uy; 0xb5uy;
    0xfbuy; 0xe9uy; 0x34uy; 0x02uy; 0xb1uy; 0x17uy; 0x67uy; 0xbeuy; 0x01uy; 0xbfuy; 0x07uy; 0x34uy; 0x44uy; 0xd6uy; 0xbauy; 0x1duy;
    0xd2uy; 0xbcuy; 0xa5uy; 0xbduy; 0x07uy; 0x4duy; 0x4auy; 0x5fuy; 0xaeuy; 0x35uy; 0x31uy; 0xaduy; 0x13uy; 0x03uy; 0xd8uy; 0x4buy;
    0x30uy; 0xd8uy; 0x97uy; 0x31uy; 0x8cuy; 0xbbuy; 0xbauy; 0x04uy; 0xe0uy; 0x3cuy; 0x2euy; 0x66uy; 0xdeuy; 0x6duy; 0x91uy; 0xf8uy;
    0x2fuy; 0x96uy; 0xeauy; 0x1duy; 0x4buy; 0xb5uy; 0x4auy; 0x5auy; 0xaeuy; 0x10uy; 0x2duy; 0x59uy; 0x46uy; 0x57uy; 0xf5uy; 0xc9uy;
    0x78uy; 0x95uy; 0x53uy; 0x51uy; 0x2buy; 0x29uy; 0x6duy; 0xeauy; 0x29uy; 0xd8uy; 0x02uy; 0x31uy; 0x96uy; 0x35uy; 0x7euy; 0x3euy;
    0x3auy; 0x6euy; 0x95uy; 0x8fuy; 0x39uy; 0xe3uy; 0xc2uy; 0x34uy; 0x40uy; 0x38uy; 0xeauy; 0x60uy; 0x4buy; 0x31uy; 0xeduy; 0xc6uy;
    0xf0uy; 0xf7uy; 0xffuy; 0x6euy; 0x71uy; 0x81uy; 0xa5uy; 0x7cuy; 0x92uy; 0x82uy; 0x6auy; 0x26uy; 0x8fuy; 0x86uy; 0x76uy; 0x8euy;
    0x96uy; 0xf8uy; 0x78uy; 0x56uy; 0x2fuy; 0xc7uy; 0x1duy; 0x85uy; 0xd6uy; 0x9euy; 0x44uy; 0x86uy; 0x12uy; 0xf7uy; 0x04uy; 0x8fuy] in
  let d : lbytes 256 = createL d in
  let p = List.Tot.map u8_from_UInt8 [
    0xcfuy; 0xd5uy; 0x02uy; 0x83uy; 0xfeuy; 0xeeuy; 0xb9uy; 0x7fuy; 0x6fuy; 0x08uy; 0xd7uy; 0x3cuy; 0xbcuy; 0x7buy; 0x38uy; 0x36uy;
    0xf8uy; 0x2buy; 0xbcuy; 0xd4uy; 0x99uy; 0x47uy; 0x9fuy; 0x5euy; 0x6fuy; 0x76uy; 0xfduy; 0xfcuy; 0xb8uy; 0xb3uy; 0x8cuy; 0x4fuy;
    0x71uy; 0xdcuy; 0x9euy; 0x88uy; 0xbduy; 0x6auy; 0x6fuy; 0x76uy; 0x37uy; 0x1auy; 0xfduy; 0x65uy; 0xd2uy; 0xafuy; 0x18uy; 0x62uy;
    0xb3uy; 0x2auy; 0xfbuy; 0x34uy; 0xa9uy; 0x5fuy; 0x71uy; 0xb8uy; 0xb1uy; 0x32uy; 0x04uy; 0x3fuy; 0xfeuy; 0xbeuy; 0x3auy; 0x95uy;
    0x2buy; 0xafuy; 0x75uy; 0x92uy; 0x44uy; 0x81uy; 0x48uy; 0xc0uy; 0x3fuy; 0x9cuy; 0x69uy; 0xb1uy; 0xd6uy; 0x8euy; 0x4cuy; 0xe5uy;
    0xcfuy; 0x32uy; 0xc8uy; 0x6buy; 0xafuy; 0x46uy; 0xfeuy; 0xd3uy; 0x01uy; 0xcauy; 0x1auy; 0xb4uy; 0x03uy; 0x06uy; 0x9buy; 0x32uy;
    0xf4uy; 0x56uy; 0xb9uy; 0x1fuy; 0x71uy; 0x89uy; 0x8auy; 0xb0uy; 0x81uy; 0xcduy; 0x8cuy; 0x42uy; 0x52uy; 0xefuy; 0x52uy; 0x71uy;
    0x91uy; 0x5cuy; 0x97uy; 0x94uy; 0xb8uy; 0xf2uy; 0x95uy; 0x85uy; 0x1duy; 0xa7uy; 0x51uy; 0x0fuy; 0x99uy; 0xcbuy; 0x73uy; 0xebuy ] in
  let p : lbytes 128 = createL p in
  let q = List.Tot.map u8_from_UInt8 [
    0xccuy; 0x4euy; 0x90uy; 0xd2uy; 0xa1uy; 0xb3uy; 0xa0uy; 0x65uy; 0xd3uy; 0xb2uy; 0xd1uy; 0xf5uy; 0xa8uy; 0xfcuy; 0xe3uy; 0x1buy;
    0x54uy; 0x44uy; 0x75uy; 0x66uy; 0x4euy; 0xabuy; 0x56uy; 0x1duy; 0x29uy; 0x71uy; 0xb9uy; 0x9fuy; 0xb7uy; 0xbeuy; 0xf8uy; 0x44uy;
    0xe8uy; 0xecuy; 0x1fuy; 0x36uy; 0x0buy; 0x8cuy; 0x2auy; 0xc8uy; 0x35uy; 0x96uy; 0x92uy; 0x97uy; 0x1euy; 0xa6uy; 0xa3uy; 0x8fuy;
    0x72uy; 0x3fuy; 0xccuy; 0x21uy; 0x1fuy; 0x5duy; 0xbcuy; 0xb1uy; 0x77uy; 0xa0uy; 0xfduy; 0xacuy; 0x51uy; 0x64uy; 0xa1uy; 0xd4uy;
    0xffuy; 0x7fuy; 0xbbuy; 0x4euy; 0x82uy; 0x99uy; 0x86uy; 0x35uy; 0x3cuy; 0xb9uy; 0x83uy; 0x65uy; 0x9auy; 0x14uy; 0x8cuy; 0xdduy;
    0x42uy; 0x0cuy; 0x7duy; 0x31uy; 0xbauy; 0x38uy; 0x22uy; 0xeauy; 0x90uy; 0xa3uy; 0x2buy; 0xe4uy; 0x6cuy; 0x03uy; 0x0euy; 0x8cuy;
    0x17uy; 0xe1uy; 0xfauy; 0x0auy; 0xd3uy; 0x78uy; 0x59uy; 0xe0uy; 0x6buy; 0x0auy; 0xa6uy; 0xfauy; 0x3buy; 0x21uy; 0x6duy; 0x9cuy;
    0xbeuy; 0x6cuy; 0x0euy; 0x22uy; 0x33uy; 0x97uy; 0x69uy; 0xc0uy; 0xa6uy; 0x15uy; 0x91uy; 0x3euy; 0x5duy; 0xa7uy; 0x19uy; 0xcfuy ] in
  let q : lbytes 128 = createL q in
  let rBlind = List.Tot.map u8_from_UInt8 [0x7buy; 0x9buy; 0xe7uy; 0xacuy; 0x73uy; 0xb4uy; 0x5cuy; 0x00uy] in
  let rBlind : lbytes 8 = createL rBlind in

  let msg = List.Tot.map u8_from_UInt8 [
    0xdduy; 0x67uy; 0x0auy; 0x01uy; 0x46uy; 0x58uy; 0x68uy; 0xaduy; 0xc9uy; 0x3fuy; 0x26uy; 0x13uy; 0x19uy; 0x57uy; 0xa5uy; 0x0cuy;
    0x52uy; 0xfbuy; 0x77uy; 0x7cuy; 0xdbuy; 0xaauy; 0x30uy; 0x89uy; 0x2cuy; 0x9euy; 0x12uy; 0x36uy; 0x11uy; 0x64uy; 0xecuy; 0x13uy;
    0x97uy; 0x9duy; 0x43uy; 0x04uy; 0x81uy; 0x18uy; 0xe4uy; 0x44uy; 0x5duy; 0xb8uy; 0x7buy; 0xeeuy; 0x58uy; 0xdduy; 0x98uy; 0x7buy;
    0x34uy; 0x25uy; 0xd0uy; 0x20uy; 0x71uy; 0xd8uy; 0xdbuy; 0xaeuy; 0x80uy; 0x70uy; 0x8buy; 0x03uy; 0x9duy; 0xbbuy; 0x64uy; 0xdbuy;
    0xd1uy; 0xdeuy; 0x56uy; 0x57uy; 0xd9uy; 0xfeuy; 0xd0uy; 0xc1uy; 0x18uy; 0xa5uy; 0x41uy; 0x43uy; 0x74uy; 0x2euy; 0x0fuy; 0xf3uy;
    0xc8uy; 0x7fuy; 0x74uy; 0xe4uy; 0x58uy; 0x57uy; 0x64uy; 0x7auy; 0xf3uy; 0xf7uy; 0x9euy; 0xb0uy; 0xa1uy; 0x4cuy; 0x9duy; 0x75uy;
    0xeauy; 0x9auy; 0x1auy; 0x04uy; 0xb7uy; 0xcfuy; 0x47uy; 0x8auy; 0x89uy; 0x7auy; 0x70uy; 0x8fuy; 0xd9uy; 0x88uy; 0xf4uy; 0x8euy;
    0x80uy; 0x1euy; 0xdbuy; 0x0buy; 0x70uy; 0x39uy; 0xdfuy; 0x8cuy; 0x23uy; 0xbbuy; 0x3cuy; 0x56uy; 0xf4uy; 0xe8uy; 0x21uy; 0xacuy] in
  let msg : lbytes 128 = createL msg in
  let salt = List.Tot.map u8_from_UInt8 [
    0x8buy; 0x2buy; 0xdduy; 0x4buy; 0x40uy; 0xfauy; 0xf5uy; 0x45uy; 0xc7uy; 0x78uy; 0xdduy; 0xf9uy; 0xbcuy; 0x1auy; 0x49uy; 0xcbuy;
    0x57uy; 0xf9uy; 0xb7uy; 0x1buy] in
  let salt : lbytes 20 = createL salt in
  let sgnt_expected = List.Tot.map u8_from_UInt8 [
    0xa4uy; 0x4euy; 0x5cuy; 0x83uy; 0xc6uy; 0xfeuy; 0xdfuy; 0x7fuy; 0x44uy; 0x33uy; 0x78uy; 0x82uy; 0x54uy; 0x2auy; 0x96uy; 0x10uy;
    0x72uy; 0x4auy; 0xa6uy; 0xf5uy; 0xb8uy; 0xf1uy; 0x3buy; 0x4fuy; 0x51uy; 0xebuy; 0x9euy; 0xf9uy; 0x84uy; 0xf5uy; 0x19uy; 0xaauy;
    0xe9uy; 0xe3uy; 0x4buy; 0x26uy; 0x4euy; 0x8duy; 0x06uy; 0xb6uy; 0x93uy; 0x66uy; 0x4duy; 0xe1uy; 0xccuy; 0xe1uy; 0x36uy; 0xd0uy;
    0x6duy; 0x10uy; 0x7fuy; 0x64uy; 0x51uy; 0x99uy; 0x8auy; 0xf9uy; 0x01uy; 0x21uy; 0x3fuy; 0xc8uy; 0x95uy; 0x83uy; 0xe6uy; 0xbeuy;
    0xfeuy; 0x1euy; 0xd1uy; 0x12uy; 0x35uy; 0xf5uy; 0xb5uy; 0xceuy; 0x8buy; 0xd4uy; 0x72uy; 0xb3uy; 0x84uy; 0xefuy; 0xf0uy; 0xcduy;
    0x80uy; 0xd3uy; 0x75uy; 0xbduy; 0x6auy; 0x88uy; 0xaeuy; 0x6fuy; 0x5buy; 0x76uy; 0x75uy; 0xc2uy; 0x50uy; 0x8buy; 0xa9uy; 0xb9uy;
    0xf0uy; 0x17uy; 0x1euy; 0x10uy; 0xc9uy; 0x58uy; 0xd4uy; 0xc0uy; 0x4cuy; 0x10uy; 0x0euy; 0xf9uy; 0x06uy; 0xccuy; 0x97uy; 0x58uy;
    0x0duy; 0xe7uy; 0x73uy; 0xaduy; 0x9duy; 0xf4uy; 0xdauy; 0x13uy; 0xd5uy; 0x95uy; 0xbeuy; 0xe2uy; 0x4auy; 0xf8uy; 0x12uy; 0x88uy;
    0x4euy; 0xd4uy; 0xdcuy; 0xe8uy; 0x09uy; 0x51uy; 0xecuy; 0xd0uy; 0x4buy; 0x1buy; 0xa6uy; 0xd7uy; 0x8cuy; 0x29uy; 0x34uy; 0xe6uy;
    0xabuy; 0x0auy; 0x77uy; 0x36uy; 0x83uy; 0x91uy; 0x1fuy; 0xccuy; 0x68uy; 0x91uy; 0x35uy; 0x37uy; 0x67uy; 0x27uy; 0x78uy; 0x09uy;
    0xecuy; 0x74uy; 0x6fuy; 0x95uy; 0x98uy; 0xe4uy; 0xf8uy; 0xf0uy; 0xcbuy; 0x1duy; 0x3duy; 0x37uy; 0x84uy; 0x3fuy; 0xeauy; 0x2auy;
    0x8cuy; 0xb0uy; 0x91uy; 0xf2uy; 0x91uy; 0x91uy; 0x22uy; 0x76uy; 0x9euy; 0xe4uy; 0x17uy; 0xdauy; 0x18uy; 0xd6uy; 0x03uy; 0xf7uy;
    0x98uy; 0x37uy; 0x0cuy; 0xaduy; 0x7buy; 0x76uy; 0x0auy; 0x7fuy; 0x57uy; 0x3auy; 0xeauy; 0xf5uy; 0x16uy; 0xa0uy; 0xf9uy; 0x0duy;
    0x95uy; 0x25uy; 0x65uy; 0xb8uy; 0xa1uy; 0x9auy; 0x8fuy; 0xc3uy; 0xf0uy; 0xeeuy; 0x7duy; 0x39uy; 0x1duy; 0x9buy; 0x8buy; 0x3fuy;
    0x98uy; 0xbeuy; 0xbbuy; 0x0duy; 0x5duy; 0x01uy; 0x0euy; 0x32uy; 0xe0uy; 0xb8uy; 0x00uy; 0xe9uy; 0x65uy; 0x6fuy; 0x64uy; 0x08uy;
    0x2buy; 0xb1uy; 0xacuy; 0x95uy; 0xa2uy; 0x23uy; 0xf4uy; 0x31uy; 0xecuy; 0x40uy; 0x6auy; 0x42uy; 0x95uy; 0x4buy; 0x2duy; 0x57uy] in
  let sgnt_expected : lbytes 256 = createL sgnt_expected in
  ctest modBits n 17 e modBits d (128*8) p (128*8) q 128 msg 20 salt rBlind sgnt_expected (4uy)

val test: unit -> ML unit
let test() =
  let res = test1() && test2() && test3() && test4() in
  if res then IO.print_string "\nSuccess!\n"
  else IO.print_string "\nFailure"
