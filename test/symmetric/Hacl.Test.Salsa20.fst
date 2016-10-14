module Hacl.Test.Salsa20

open FStar.Buffer

val main: unit -> ST FStar.Int32.t
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let main () =
  push_frame();
  let len = 512ul in
  let keysize = 32ul in
  let noncesize = 8ul in
  let ciphertext = create 0uy len in
  let plaintext = create 0uy len in
  let expected1 = createL [
    0xE3uy; 0xBEuy; 0x8Fuy; 0xDDuy; 0x8Buy; 0xECuy; 0xA2uy; 0xE3uy; 0xEAuy; 0x8Euy; 0xF9uy; 0x47uy; 0x5Buy; 0x29uy; 0xA6uy; 0xE7uy;
    0x00uy; 0x39uy; 0x51uy; 0xE1uy; 0x09uy; 0x7Auy; 0x5Cuy; 0x38uy; 0xD2uy; 0x3Buy; 0x7Auy; 0x5Fuy; 0xADuy; 0x9Fuy; 0x68uy; 0x44uy;
    0xB2uy; 0x2Cuy; 0x97uy; 0x55uy; 0x9Euy; 0x27uy; 0x23uy; 0xC7uy; 0xCBuy; 0xBDuy; 0x3Fuy; 0xE4uy; 0xFCuy; 0x8Duy; 0x9Auy; 0x07uy;
    0x44uy; 0x65uy; 0x2Auy; 0x83uy; 0xE7uy; 0x2Auy; 0x9Cuy; 0x46uy; 0x18uy; 0x76uy; 0xAFuy; 0x4Duy; 0x7Euy; 0xF1uy; 0xA1uy; 0x17uy
    ] in
  let expected2 = createL [
    0x57uy; 0xBEuy; 0x81uy; 0xF4uy; 0x7Buy; 0x17uy; 0xD9uy; 0xAEuy; 0x7Cuy; 0x4Fuy; 0xF1uy; 0x54uy; 0x29uy; 0xA7uy; 0x3Euy; 0x10uy;
    0xACuy; 0xF2uy; 0x50uy; 0xEDuy; 0x3Auy; 0x90uy; 0xA9uy; 0x3Cuy; 0x71uy; 0x13uy; 0x08uy; 0xA7uy; 0x4Cuy; 0x62uy; 0x16uy; 0xA9uy;
    0xEDuy; 0x84uy; 0xCDuy; 0x12uy; 0x6Duy; 0xA7uy; 0xF2uy; 0x8Euy; 0x8Auy; 0xBFuy; 0x8Buy; 0xB6uy; 0x35uy; 0x17uy; 0xE1uy; 0xCAuy;
    0x98uy; 0xE7uy; 0x12uy; 0xF4uy; 0xFBuy; 0x2Euy; 0x1Auy; 0x6Auy; 0xEDuy; 0x9Fuy; 0xDCuy; 0x73uy; 0x29uy; 0x1Fuy; 0xAAuy; 0x17uy
    ] in
  let expected3 = createL [
    0x95uy; 0x82uy; 0x11uy; 0xC4uy; 0xBAuy; 0x2Euy; 0xBDuy; 0x58uy; 0x38uy; 0xC6uy; 0x35uy; 0xEDuy; 0xB8uy; 0x1Fuy; 0x51uy; 0x3Auy;
    0x91uy; 0xA2uy; 0x94uy; 0xE1uy; 0x94uy; 0xF1uy; 0xC0uy; 0x39uy; 0xAEuy; 0xECuy; 0x65uy; 0x7Duy; 0xCEuy; 0x40uy; 0xAAuy; 0x7Euy;
    0x7Cuy; 0x0Auy; 0xF5uy; 0x7Cuy; 0xACuy; 0xEFuy; 0xA4uy; 0x0Cuy; 0x9Fuy; 0x14uy; 0xB7uy; 0x1Auy; 0x4Buy; 0x34uy; 0x56uy; 0xA6uy;
    0x3Euy; 0x16uy; 0x2Euy; 0xC7uy; 0xD8uy; 0xD1uy; 0x0Buy; 0x8Fuy; 0xFBuy; 0x18uy; 0x10uy; 0xD7uy; 0x10uy; 0x01uy; 0xB6uy; 0x18uy
    ] in
  let expected4 = createL [
    0x69uy; 0x6Auy; 0xFCuy; 0xFDuy; 0x0Cuy; 0xDDuy; 0xCCuy; 0x83uy; 0xC7uy; 0xE7uy; 0x7Fuy; 0x11uy; 0xA6uy; 0x49uy; 0xD7uy; 0x9Auy;
    0xCDuy; 0xC3uy; 0x35uy; 0x4Euy; 0x96uy; 0x35uy; 0xFFuy; 0x13uy; 0x7Euy; 0x92uy; 0x99uy; 0x33uy; 0xA0uy; 0xBDuy; 0x6Fuy; 0x53uy;
    0x77uy; 0xEFuy; 0xA1uy; 0x05uy; 0xA3uy; 0xA4uy; 0x26uy; 0x6Buy; 0x7Cuy; 0x0Duy; 0x08uy; 0x9Duy; 0x08uy; 0xF1uy; 0xE8uy; 0x55uy;
    0xCCuy; 0x32uy; 0xB1uy; 0x5Buy; 0x93uy; 0x78uy; 0x4Auy; 0x36uy; 0xE5uy; 0x6Auy; 0x76uy; 0xCCuy; 0x64uy; 0xBCuy; 0x84uy; 0x77uy
    ] in
  let key = create 0uy keysize in
  key.(0ul) <- 0x80uy;
  let nonce = create 0uy noncesize in
  (* let chacha20 = createL [ *)
  (*   43y; 68y; 61y; 63y; 68y; 61y; 32y; 30y *)
  (* ] in *)
  Hacl.Symmetric.Salsa20.salsa20_encrypt ciphertext key nonce plaintext len;
  C.compare_and_print2 (* chacha20 *) expected1 (offset ciphertext 0ul) 64ul;
  C.compare_and_print2 (* chacha20 *) expected2 (offset ciphertext 192ul) 64ul;
  C.compare_and_print2 (* chacha20 *) expected3 (offset ciphertext 256ul) 64ul;
  C.compare_and_print2 (* chacha20 *) expected4 (offset ciphertext 448ul) 64ul;
  pop_frame();
  C.exit_success
