open Marlin_plonk_bindings

exception PayloadLength of string

let%test_module "TLS Notary test" =
(
    module struct
    let () =
      Zexe_backend.Pasta.Vesta_based_plonk_plookup.Keypair.set_urs_info
        [On_disk {directory= "/tmp/"; should_write= true}]

    (*
      Zk-Snark implemented here allows proving the following:

      Given:
        1. Signature Scheme base EC point
        2. [2^n] multiple of the base point (where n is the bit-size of the base field elements).
          This is needed only for the circuit optimization
        3. TlsNotary public key EC point
      as public inputs,

      Prover knows:
        1. TLS session ciphertext: CT
        2. AES server key computed from TLS session master secret: KEY
        3. AES initialization vector computed from TLS session master secret: IV
        4. TlsNotary signature: (P, S)

      such that:
        1. Having computed AES key schedule KEY -> KS
        2. Having computed GCM hash key KS -> HK
        3. Having decrypted cyphertext into plaintext (CT, KS, IV) -> PT
        4. Having computed cyphertext authentication tag (CT, HK) -> AT
        4. Having hashed the data (KEY, IV, AT, P) -> E
        5. Score value from plaintext PT is above the threshold value
        6. TlsNotary signature (P, S) verifies against:
          a. TlsNotary public key
          b. S, E scalars

      Prover computation for this SNARK includes the complete TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256
      TLS cipher GCM-AES functionality
    *)

    module TlsNotarySignature
        (Impl : Snarky.Snark_intf.Run with type prover_state = unit and type field = Pasta_fp.t)
        (Params : sig val params : Impl.field Sponge.Params.t end)
    = struct
      open Core
      open Impl
      open Snarky.Snark_intf

      type witness =
      {
        (* cipher_text: int array; *)
        server_records0: int array;
        server_records1: int array;
        client_cwk_share: int array;
        client_civ_share: int array;
        client_swk_share: int array;
        client_siv_share: int array;
        client_pms_share: int array;
        client_req_cipher: int array;
        notary_cwk_share: int array;
        notary_civ_share: int array;
        notary_swk_share: int array;
        notary_siv_share: int array;
        (* encryption_key : int array; *)
        (* iv: int array; *)
        notary_pms_share: int array;
        notary_time: int array;
        ephemeral_pubkey: int array;
        ephemeral_pubkey_valid_from: int array;
        ephemeral_pubkey_valid_until: int array;
        notary_pubkey: int array;
        session_sig: int array;
        esmk: int array;
        (* signature: (Field.Constant.t * Field.Constant.t) * Field.Constant.t *)
        sha256_1: int array;
        sha256_2: int array;
      }

      let authentication ?witness (p, pn, q) () =

        let module Block = Plonk.Bytes.Block (Impl) in
        let module Bytes = Plonk.Bytes.Constraints (Impl) in
        let module Sponge = Plonk.Poseidon.ArithmeticSponge (Impl) (Params) in
        let module Ecc = Plonk.Ecc.Constraints (Impl) in
        let module Ec = Ecc.Basic in

        Random.full_init [|7|];

        let int_array_witness ~length f =
          exists (Typ.array ~length Field.typ)
            ~compute:(fun () -> Array.map ~f:Field.Constant.of_int (f (Option.value_exn witness)))
        in
        
        let server_records0_len = Array.length Test.server_records0 in
        let server_records1_len = Array.length Test.server_records1 in
        let client_req_cipher_len = Array.length Test.client_req_cipher in
        let ctl = server_records0_len - 8 in
        let bloks = (ctl + 15) / 16 in

        let server_records0 = int_array_witness ~length:server_records0_len (fun w -> w.server_records0) in
        let server_records1 = int_array_witness ~length:server_records1_len (fun w -> w.server_records1) in
        let client_cwk_share = int_array_witness ~length:16 (fun w -> w.client_cwk_share) in
        let client_civ_share = int_array_witness ~length:4 (fun w -> w.client_civ_share) in
        let client_swk_share = int_array_witness ~length:16 (fun w -> w.client_swk_share) in
        let client_siv_share = int_array_witness ~length:4 (fun w -> w.client_siv_share) in
        let client_pms_share = int_array_witness ~length:32 (fun w -> w.client_pms_share) in
        let client_req_cipher = int_array_witness ~length:client_req_cipher_len (fun w -> w.client_req_cipher) in
        let notary_cwk_share = int_array_witness ~length:16 (fun w -> w.notary_cwk_share) in
        let notary_civ_share = int_array_witness ~length:4 (fun w -> w.notary_civ_share) in
        let notary_swk_share = int_array_witness ~length:16 (fun w -> w.notary_swk_share) in
        let notary_siv_share = int_array_witness ~length:4 (fun w -> w.notary_siv_share) in
        let notary_pms_share = int_array_witness ~length:32 (fun w -> w.notary_pms_share) in
        let notary_time = int_array_witness ~length:8 (fun w -> w.notary_time) in
        let ephemeral_pubkey = int_array_witness ~length:65 (fun w -> w.ephemeral_pubkey) in
        let ephemeral_pubkey_valid_from = int_array_witness ~length:4 (fun w -> w.ephemeral_pubkey_valid_from) in
        let ephemeral_pubkey_valid_until = int_array_witness ~length:4 (fun w -> w.ephemeral_pubkey_valid_until) in
        let notary_pubkey = int_array_witness ~length:65 (fun w -> w.notary_pubkey) in
        let session_sig = int_array_witness ~length:64 (fun w -> w.session_sig) in
        let esmk = int_array_witness ~length:64 (fun w -> w.esmk) in

        (* TODO: when sha256 is implemented in circuit, these can be calculated *)
        let sha256_1 = int_array_witness ~length:32 (fun w -> w.sha256_1) in
        let sha256_2 = int_array_witness ~length:32 (fun w -> w.sha256_2) in
        
        (* let n = Bigint.to_field (Bigint.of_decimal_string "115792089210356248762697446949407573529996955224135760342422259061068512044369") in *)
        (* n = n1, n2. The value of n = n1*2**128 + n2 *)
        let n = (Bigint.to_field (Bigint.of_decimal_string "340282366841710300967557013911933812735")), (Bigint.to_field (Bigint.of_decimal_string "251094175845612772866266697226726352209")) in
        let two_128 = Bigint.to_bignum_bigint (Bigint.of_decimal_string "340282366920938463463374607431768211456") in
        let bigint2u256 a =
          let low = (Bignum_bigint.(%) a two_128) in
          let high = (Bignum_bigint.(/) a two_128) in
          let _ = Printf.printf "kkk %s %s %s" (Bignum_bigint.to_string a) (Bignum_bigint.to_string two_128) (Bignum_bigint.to_string high) in 
          let low_field = (Bigint.to_field (Bigint.of_bignum_bigint low)) in
          let high_field = (Bigint.to_field (Bigint.of_bignum_bigint high)) in
          if high < two_128 then (high_field, low_field) else failwith "overflow" in
        let u2562bigint a =
          let low = (Bigint.to_bignum_bigint (Bigint.of_field (snd a))) in
          let high = (Bigint.to_bignum_bigint (Bigint.of_field (fst a))) in
          Bignum_bigint.(+) (Bignum_bigint.( * ) high two_128) low in
            
        let rec gcd_ext a b =
          if Bignum_bigint.zero = b then (Bignum_bigint.one, Bignum_bigint.zero, a)
          else let s, t, g = gcd_ext b (Bignum_bigint.(%) a b) in
              (t, Bignum_bigint.(-) s (Bignum_bigint.( * ) (Bignum_bigint.(/) a b) t), g) in
        let invmod a m =
          let mk_pos x = if x < Bignum_bigint.zero then Bignum_bigint.(+) x m else x in
          let i,_,r = gcd_ext a m in
          if r = Bignum_bigint.one then mk_pos i else failwith "invmod" in

        (* let ecdsa_p256_sig_check ~pubkey ~r ~s ~h =
          let inv_s =  *)

        (* TODO: ecdsa p-256 sig verfication *)
        (* python equivalent code: *)
        (* pubkey: (big_endian_bytes_to_int(notary_pubkey[1..33]), big_endian_bytes_to_int(notary_pubkey([33..65])) *)
        (* r: (big_endian_bytes_to_int(esmk[0..32])) *)
        (* s: (big_endian_bytes_to_int(esmk[32..64])) *)
        (* h: sha256_2 *)
        (* also need to check(ephemeral_pubkey, session_sig[0..32], session_sig[32..64], sha256_1) *)
        (* def check(pubkey, r, s, h):
          inv_s = libnum.invmod(s,curve.n)
          c = inv_s
          u1=(h*c) % curve.n
          u2=(r*c) % curve.n
          P = point_add(scalar_mult(u1,curve.g), scalar_mult(u2,pubkey))
          res = P[0] % curve.n
          return res==r *)

        (* CIPHERTEXT *)
        (*let ctl = Array.length (Option.value_exn witness).cipher_text in*)
        (* let ctl = Array.length Test.ct - 8 in *)
        (* let ct =
          int_array_witness ~length:ctl
            (fun w -> w.ct)
        in *)
        let ct = Array.sub server_records0 8 ctl in

        (* AES SERVER ENCRYPTION KEY *)
        let key = Array.mapi client_swk_share ~f:(fun i x -> Bytes.xor x notary_swk_share.(i)) in

        (* AES INITIALIZATION VECTOR *)
        let iv_first4 = Array.mapi client_siv_share ~f:(fun i x -> Bytes.xor x notary_siv_share.(i)) in
        let iv_next8 = Array.sub server_records0 0 8 in
        let iv = Array.concat [iv_first4; iv_next8; [|Field.zero; Field.zero; Field.zero; Field.zero|]] in

        (* TLS NOTARY SIGNATURE *)
        (* let (rc, s) =
          exists Typ.( (field * field) * field)
            ~compute:(fun () -> (Option.value_exn witness).signature)
        in *)
        let s1 = session_sig in
        let s2 = esmk in

        (* compute AES key schedule *)
        let ks = Block.expandKey key in

        (* compute GCM hash key *)
        let h = Block.encryptBlock (Array.init 16 ~f:(fun _ -> Field.zero)) ks in

        (* initialize/encrypt GCM counters *)
        let ec0 = Array.copy iv in
        Array.iteri [|0;0;0;1|] ~f:(fun i x -> ec0.(i+12) <- Field.of_int x);
        let ec0 = Block.encryptBlock ec0 ks in
        let ptdl1 = 2 in
        let ec = Array.init ptdl1 ~f:(fun i -> 
        (
          let cnt = Array.copy iv in
          let i = i + bloks - ptdl1 + 2 in
          Array.iteri Int.[|i lsr 24; (i lsr 16) land 255; (i lsr 8) land 255; i land 255;|]
            ~f:(fun j x -> cnt.(j + 12) <- Field.of_int x);
          Block.encryptBlock cnt ks
        )) in

        (* decrypt score ciphertext into plaintext and decode *)
        (* let score = let offset = ctl-9-(bloks-ptdl1)*16 in Array.mapi (Array.sub ct (ctl-9) 3)
          ~f:(fun i x -> Bytes.asciiDigit (Bytes.xor ec.((offset+i)/16).((offset+i)%16) x)) in *)
        
        (* check the score *)
        (* Bytes.assertScore Field.(score.(0) * (of_int 100) + score.(1) * (of_int 10) + score.(2)); *)

        (* pad ciphertext to the block boundary *)
        let ctp = Array.append ct (Array.init (bloks*16-ctl) ~f:(fun _ -> Field.zero)) in
        let ctp = Array.init bloks ~f:(fun i -> Array.sub ctp (i*16) 16) in
        
        (* compute GCM ciphertext authentication tag *)
        let len = Array.init 16 ~f:(fun _ -> Field.zero)  in
        Array.iteri ~f:(fun i x -> len.(i + 12) <- Field.of_int x)
          [|((ctl*8) lsr 24) land 255; ((ctl*8) lsr 16) land 255; ((ctl*8) lsr 8) land 255; (ctl*8) land 255;|];
        let ctp = Array.append ctp [|len|] in

        let at = Array.foldi (Array.append ctp [|len|]) ~init:(Array.init 16 ~f:(fun _ -> Field.zero))
          ~f:(fun i ht bl ->
            let htn = Block.mul (Block.xor ht bl) h in
            if i <= bloks then htn
            else ht
          ) in
        
        let at = Block.xor ec0 at in

(*      just vrifying the hash-tag correctness
        let ttt = [|0xf4; 0x7c; 0x28; 0x7d; 0xe1; 0x23; 0x5e; 0x6c; 0x1c; 0x58; 0xd0; 0xb1; 0x80; 0xad; 0x12; 0x98;|] in
        for i = 0 to 15 do
          assert_ (Snarky.Constraint.equal at.(i) (Field.of_int ttt.(i)));
        done;
*)
        (* hash the data to be signed *)
        (* let hb = Array.map ~f:(fun x -> Bytes.b16tof x) [|key; iv; at|] in
        Array.iter ~f:(fun x -> Sponge.absorb x) (Array.append hb [|fst rc; snd rc;|]);
        let e = Sponge.squeeze in *)

        (* verify TlsNotary signature *)
        (* let lpt = Ecc.add (Ecc.mul q e) rc in
        let rpt = Ecc.sub (Ecc.scale_pack p s) pn in
        assert_ (Snarky.Constraint.equal (fst lpt) (fst lpt));
        assert_ (Snarky.Constraint.equal (snd rpt) (snd rpt)); *)
        (* let test_s = Bigint.to_field (Bigint.of_decimal_string "86010965201271384069584565278387931067403690992144386669414930219218076294718") in
         *)
        let test_s = (Bigint.to_field (Bigint.of_decimal_string "252763509257167167559539568902980276620")), (Bigint.to_field (Bigint.of_decimal_string "108392074650980745770071854956543335998")) in
        let test_inv_s = (Bigint.to_field (Bigint.of_decimal_string "304709078428790393539962802780933455242")), (Bigint.to_field (Bigint.of_decimal_string "129215936266307296341781209091068309292")) in
        let calc_inv_s = (bigint2u256 (invmod (u2562bigint test_s) (u2562bigint n))) in
        assert_ (Snarky.Constraint.equal (Field.constant (fst calc_inv_s)) (Field.constant (fst test_inv_s)));
        assert_ (Snarky.Constraint.equal (Field.constant (snd calc_inv_s)) (Field.constant (snd test_inv_s)));
        ()

      module Public_input = Test.Public_input (Impl)
      open Public_input
      let input () = 
        let open Typ in
        Impl.Data_spec.
        [
          tuple3
            (tuple2 Field.typ Field.typ)  (* signature scheme base point P *)
            (tuple2 Field.typ Field.typ)  (* [n]P where n = field elements size in bits *)
            (tuple2 Field.typ Field.typ)  (* notary public key *)
        ]

      let keys = Impl.generate_keypair ~exposing:(input ()) authentication

      let proof =
        (* let signature =
          (* Just converting the signature from strings *)
          let ((x, y), s) = Test.sign in
          Bigint.((to_field (of_decimal_string x), to_field (of_decimal_string y)), to_field (of_decimal_string s))
        in *)
        Impl.prove (Impl.Keypair.pk keys) (input ())
          (authentication
             ~witness:{
               server_records0= Test.server_records0;
               server_records1= Test.server_records1;
               client_cwk_share= Test.client_cwk_share;
               client_civ_share= Test.client_civ_share;
               client_swk_share= Test.client_swk_share;
               client_siv_share= Test.client_siv_share;
               client_pms_share= Test.client_pms_share;
               client_req_cipher= Test.client_req_cipher;
               notary_cwk_share= Test.notary_cwk_share;
               notary_civ_share= Test.notary_civ_share;
               notary_swk_share= Test.notary_swk_share;
               notary_siv_share= Test.notary_siv_share;
               notary_pms_share= Test.notary_pms_share;
               notary_time= Test.notary_time;
               ephemeral_pubkey= Test.ephemeral_pubkey;
               ephemeral_pubkey_valid_from= Test.ephemeral_pubkey_valid_from;
               ephemeral_pubkey_valid_until= Test.ephemeral_pubkey_valid_until;
               notary_pubkey= Test.notary_pubkey;
               session_sig= Test.session_sig;
               esmk= Test.esmk;
               sha256_1= Test.sha256_1;
               sha256_2= Test.sha256_2;
               (* cipher_text= Test.ct;
               encryption_key= Test.key;
               iv= Test.iv;
               signature *)
             } )
          ()
          public_input
      let%test_unit "check backend GcmAuthentication proof" =
        assert (Impl.verify proof (Impl.Keypair.vk keys) (input ()) public_input)
    end

    module Impl = Snarky.Snark.Run.Make(Zexe_backend.Pasta.Vesta_based_plonk_plookup) (Core.Unit)
    module Params = struct let params = Sponge.Params.(map pasta_p5 ~f:Impl.Field.Constant.of_string) end
    include TlsNotarySignature (Impl) (Params) 
  end
)
