open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_RSAPSS2048_SHA256_rsapss_sign =
      foreign "Hacl_RSAPSS2048_SHA256_rsapss_sign"
        (uint32_t @->
           (uint32_t @->
              ((ptr uint64_t) @->
                 (uint32_t @->
                    (ocaml_bytes @->
                       (uint32_t @->
                          (ocaml_bytes @-> (ocaml_bytes @-> (returning bool)))))))))
    let hacl_RSAPSS2048_SHA256_rsapss_verify =
      foreign "Hacl_RSAPSS2048_SHA256_rsapss_verify"
        (uint32_t @->
           ((ptr uint64_t) @->
              (uint32_t @->
                 (uint32_t @->
                    (ocaml_bytes @->
                       (uint32_t @-> (ocaml_bytes @-> (returning bool))))))))
    let hacl_RSAPSS2048_SHA256_new_rsapss_load_pkey =
      foreign "Hacl_RSAPSS2048_SHA256_new_rsapss_load_pkey"
        (uint32_t @->
           (ocaml_bytes @-> (ocaml_bytes @-> (returning (ptr uint64_t)))))
    let hacl_RSAPSS2048_SHA256_new_rsapss_load_skey =
      foreign "Hacl_RSAPSS2048_SHA256_new_rsapss_load_skey"
        (uint32_t @->
           (uint32_t @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (ocaml_bytes @-> (returning (ptr uint64_t)))))))
    let hacl_RSAPSS2048_SHA256_rsapss_skey_sign =
      foreign "Hacl_RSAPSS2048_SHA256_rsapss_skey_sign"
        (uint32_t @->
           (uint32_t @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (ocaml_bytes @->
                       (uint32_t @->
                          (ocaml_bytes @->
                             (uint32_t @->
                                (ocaml_bytes @->
                                   (ocaml_bytes @-> (returning bool)))))))))))
    let hacl_RSAPSS2048_SHA256_rsapss_pkey_verify =
      foreign "Hacl_RSAPSS2048_SHA256_rsapss_pkey_verify"
        (uint32_t @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (uint32_t @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (uint32_t @-> (ocaml_bytes @-> (returning bool)))))))))
  end