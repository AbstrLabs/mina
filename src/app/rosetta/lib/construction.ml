open Core_kernel
open Async
open Rosetta_lib

(* Rosetta_models.Currency shadows our Currency so we "save" it as MinaCurrency first *)
module Mina_currency = Currency
open Rosetta_models
module Signature = Mina_base.Signature
module Transaction = Rosetta_lib.Transaction
module Public_key = Signature_lib.Public_key
module Signed_command_payload = Mina_base.Signed_command_payload
module User_command = Mina_base.User_command
module Signed_command = Mina_base.Signed_command
module Transaction_hash = Mina_base.Transaction_hash

module Get_options_metadata =
[%graphql
{|
    query get_options_metadata($sender: PublicKey!, $token_id: TokenId, $receiver_key: PublicKey!) {
      bestChain(maxLength: 5) {
        transactions {
          userCommands {
            fee @bsDecoder(fn: "Decoders.uint64")
          }
        }
      }

      receiver: account(publicKey: $receiver_key, token: $token_id) {
        nonce
      }

      account(publicKey: $sender, token: $token_id) {
        balance {
          blockHeight @bsDecoder(fn: "Decoders.uint32")
          stateHash
        }
        nonce
      }
      daemonStatus {
        chainId
      }
      initialPeers
     }
|}]

module Send_payment =
[%graphql
{|
  mutation send($from: PublicKey!, $to_: PublicKey!, $token: UInt64, $amount: UInt64, $fee: UInt64, $validUntil: UInt64, $memo: String, $nonce: UInt32!, $signature: String!) {
    sendPayment(signature: {rawSignature: $signature}, input: {from: $from, to:$to_, token:$token, amount:$amount, fee:$fee, validUntil: $validUntil, memo: $memo, nonce:$nonce}) {
      payment {
        hash
      }
  }}
  |}]

module Send_delegation =
[%graphql
{|
mutation ($sender: PublicKey!,
          $receiver: PublicKey!,
          $fee: UInt64!,
          $nonce: UInt32!,
          $memo: String,
          $signature: String!) {
  sendDelegation(signature: {rawSignature: $signature}, input:
    {from: $sender, to: $receiver, fee: $fee, memo: $memo, nonce: $nonce}) {
    delegation {
      hash
    }
  }
}
|}]

module Send_create_token =
[%graphql
{|
mutation ($sender: PublicKey,
          $receiver: PublicKey!,
          $fee: UInt64!,
          $nonce: UInt32,
          $memo: String,
          $signature: String!) {
  createToken(signature: {rawSignature: $signature}, input:
    {feePayer: $sender, tokenOwner: $receiver, fee: $fee, nonce: $nonce, memo: $memo}) {
    createNewToken {
      hash
    }
  }
}
|}]

module Send_create_token_account =
[%graphql
{|
mutation ($sender: PublicKey,
          $tokenOwner: PublicKey!,
          $receiver: PublicKey!,
          $token: TokenId!,
          $fee: UInt64!,
          $nonce: UInt32,
          $memo: String,
          $signature: String!) {
  createTokenAccount(signature: {rawSignature: $signature}, input:
    {feePayer: $sender, tokenOwner: $tokenOwner, receiver: $receiver, token: $token, fee: $fee, nonce: $nonce, memo: $memo}) {
    createNewTokenAccount {
      hash
    }
  }
}
|}]

module Send_mint_tokens =
[%graphql
{|
mutation ($sender: PublicKey!,
          $receiver: PublicKey,
          $token: TokenId!,
          $amount: UInt64!,
          $fee: UInt64!,
          $nonce: UInt32,
          $memo: String,
          $signature: String!) {
  mintTokens(signature: {rawSignature: $signature}, input:
    {tokenOwner: $sender, receiver: $receiver, token: $token, amount: $amount, fee: $fee, nonce: $nonce, memo: $memo}) {
    mintTokens {
      hash
    }
  }
}
|}]

module Options = struct
  type t =
    { sender : Public_key.Compressed.t
    ; token_id : Unsigned.UInt64.t
    ; receiver : Public_key.Compressed.t
    ; valid_until : Unsigned_extended.UInt32.t option
    ; memo : string option
    }

  module Raw = struct
    type t =
      { sender : string
      ; token_id : string
      ; receiver : string
      ; valid_until : string option [@default None]
      ; memo : string option [@default None]
      }
    [@@deriving yojson]
  end

  let to_json t =
    { Raw.sender = Public_key.Compressed.to_base58_check t.sender
    ; token_id = Unsigned.UInt64.to_string t.token_id
    ; receiver = Public_key.Compressed.to_base58_check t.receiver
    ; valid_until =
        Option.map ~f:Unsigned_extended.UInt32.to_string t.valid_until
    ; memo = t.memo
    }
    |> Raw.to_yojson

  let of_json r =
    Raw.of_yojson r
    |> Result.map_error ~f:(fun e ->
           Errors.create ~context:"Options of_json" (`Json_parse (Some e)))
    |> Result.bind ~f:(fun (r : Raw.t) ->
           let open Result.Let_syntax in
           let error which e =
              Errors.create
                ~context:("Options of_json bad public key (" ^ which ^ ")")
                (`Json_parse (Some (Core_kernel.Error.to_string_hum e)))
           in
           let%bind sender =
             Public_key.Compressed.of_base58_check r.sender
             |> Result.map_error ~f:(error "sender")
           in
           let%map receiver =
             Public_key.Compressed.of_base58_check r.receiver
             |> Result.map_error ~f:(error "receiver")
           in
           { sender
           ; token_id = Unsigned.UInt64.of_string r.token_id
           ; receiver
           ; valid_until =
               Option.map ~f:Unsigned_extended.UInt32.of_string r.valid_until
           ; memo = r.memo
           })
end

(* TODO: unify handling of json between this and Options (above) and everything else in rosetta *)
module Metadata_data = struct
  type t =
    { sender : string
    ; nonce : Unsigned_extended.UInt32.t
    ; token_id : Unsigned_extended.UInt64.t
    ; receiver : string
    ; account_creation_fee : Unsigned_extended.UInt64.t option [@default None]
    ; valid_until : Unsigned_extended.UInt32.t option [@default None]
    ; memo : string option [@default None]
    }
  [@@deriving yojson]

  let create ~nonce ~sender ~token_id ~receiver ~account_creation_fee
      ~valid_until ~memo =
    { sender = Public_key.Compressed.to_base58_check sender
    ; nonce
    ; token_id
    ; receiver = Public_key.Compressed.to_base58_check receiver
    ; account_creation_fee
    ; valid_until
    ; memo
    }

  let of_json r =
    of_yojson r
    |> Result.map_error ~f:(fun e ->
           Errors.create ~context:"Options of_json" (`Json_parse (Some e)))
end

module Derive = struct
  module Env = struct
    module T (M : Monad_fail.S) = struct
      type t = { lift : 'a 'e. ('a, 'e) Result.t -> ('a, 'e) M.t }
    end

    module Real = T (Deferred.Result)
    module Mock = T (Result)

    let real : Real.t = { lift = Deferred.return }

    let mock : Mock.t = { lift = Fn.id }
  end

  module Impl (M : Monad_fail.S) = struct
    module Token_id_decode = Amount_of.Token_id.T (M)

    let handle ~(env : Env.T(M).t) (req : Construction_derive_request.t) =
      let open M.Let_syntax in
      let%bind pk =
        let pk_or_error =
          try Ok (Rosetta_coding.Coding.to_public_key req.public_key.hex_bytes)
          with exn -> Error (Core_kernel.Error.of_exn exn)
        in
        env.lift
        @@ Result.map_error
             ~f:(fun _ -> Errors.create `Malformed_public_key)
             pk_or_error
      in
      let%map token_id = Token_id_decode.decode req.metadata in
      { Construction_derive_response.address = None
      ; account_identifier =
          Some
            (User_command_info.account_id
               (`Pk Public_key.(compress pk |> Compressed.to_base58_check))
               (Option.value ~default:Amount_of.Token_id.default token_id))
      ; metadata = None
      }
  end

  module Real = Impl (Deferred.Result)
  module Mock = Impl (Result)
end

module Metadata = struct
  module Env = struct
    module T (M : Monad_fail.S) = struct
      type 'gql t =
        { gql :
               ?token_id:Unsigned.UInt64.t
            -> address:Public_key.Compressed.t
            -> receiver:Public_key.Compressed.t
            -> unit
            -> ('gql, Errors.t) M.t
        ; validate_network_choice :
               network_identifier:Network_identifier.t
            -> graphql_uri:Uri.t
            -> (unit, Errors.t) M.t
        ; lift : 'a 'e. ('a, 'e) Result.t -> ('a, 'e) M.t
        }
    end

    module Real = T (Deferred.Result)
    module Mock = T (Result)

    let real : graphql_uri:Uri.t -> 'gql Real.t =
     fun ~graphql_uri ->
      { gql =
          (fun ?token_id:_ ~address ~receiver () ->
            Graphql.query
              (Get_options_metadata.make
                 ~sender:
                   (`String (Public_key.Compressed.to_base58_check address))
                   (* for now, nonce is based on the fee payer's account using the default token,
                      per @mrmr1993
                   *)
                 ~token_id:
                   (`String Mina_base.Token_id.(default |> to_string))
                   (* WAS:
                      ( match token_id with
                      | Some x ->
                          `String (Unsigned.UInt64.to_string x)
                      | None ->
                          `Null )
                   *)
                 ~receiver_key:
                   (`String (Public_key.Compressed.to_base58_check receiver))
                 ())
              graphql_uri)
      ; validate_network_choice = Network.Validate_choice.Real.validate
      ; lift = Deferred.return
      }
  end

  (* Invariant: fees is sorted *)
  module type Field_like = sig
    type t

    val of_int : int -> t

    val ( + ) : t -> t -> t

    val ( - ) : t -> t -> t

    val ( * ) : t -> t -> t

    val ( / ) : t -> t -> t
  end

  let suggest_fee (type a) (module F : Field_like with type t = a) fees =
    let len = Array.length fees in
    let med = fees.(len / 2) in
    let iqr =
      let threeq = fees.(3 * len / 4) in
      let oneq = fees.(len / 4) in
      F.(threeq - oneq)
    in
    let open F in
    med + (iqr / of_int 2)

  let%test_unit "suggest_fee is reasonable" =
    let sugg =
      suggest_fee (module Int) [| 100; 200; 300; 400; 500; 600; 700; 800 |]
    in
    [%test_eq: int] sugg 700

  module Impl (M : Monad_fail.S) = struct
    let handle ~graphql_uri ~(env : 'gql Env.T(M).t)
        (req : Construction_metadata_request.t) =
      let open M.Let_syntax in
      let%bind req_options =
        match req.options with
        | Some options ->
            M.return options
        | None ->
            M.fail (Errors.create `No_options_provided)
      in
      let%bind options = Options.of_json req_options |> env.lift in
      let%bind res =
        env.gql ~token_id:options.token_id ~address:options.sender
          ~receiver:options.receiver ()
      in
      let%bind () =
        env.validate_network_choice ~network_identifier:req.network_identifier
          ~graphql_uri
      in
      let%bind account =
        match res#account with
        | None ->
            M.fail
              (Errors.create
                 (`Account_not_found
                   (Public_key.Compressed.to_base58_check options.sender)))
        | Some account ->
            M.return account
      in
      let nonce =
        Option.map
          ~f:(fun nonce -> Unsigned.UInt32.of_string nonce)
          account#nonce
        |> Option.value ~default:Unsigned.UInt32.zero
      in
      (* suggested fee *)
      (* Take the median of all the fees in blocks and add a bit extra using
       * the interquartile range *)
      let%map suggested_fee =
        let%map fees =
          match res#bestChain with
          | Some chain ->
              let a =
                Array.fold chain ~init:[] ~f:(fun fees block ->
                    Array.fold block#transactions#userCommands ~init:fees
                      ~f:(fun fees (`UserCommand cmd) -> cmd#fee :: fees))
                |> Array.of_list
              in
              Array.sort a ~compare:Unsigned_extended.UInt64.compare ;
              M.return a
          | None ->
              M.fail (Errors.create `Chain_info_missing)
        in
        Amount_of.mina
          (suggest_fee
             ( module struct
               include Unsigned_extended.UInt64
               include Infix
             end )
             fees)
      in
      (* minimum fee : Pull this from the compile constants *)
      let amount_metadata =
        `Assoc
          [ ( "minimum_fee"
            , Amount.to_yojson
                (Amount_of.mina
                   (Mina_currency.Fee.to_uint64
                      Mina_compile_config.minimum_user_command_fee)) )
          ]
      in
      let receiver_exists =
        Option.is_some res#receiver
      in
      let constraint_constants =
        Genesis_constants.Constraint_constants.compiled
      in
      { Construction_metadata_response.metadata =
          Metadata_data.create ~sender:options.Options.sender
            ~token_id:options.Options.token_id ~nonce ~receiver:options.receiver
            ~account_creation_fee:
              ( if receiver_exists then None
              else
                Some
                  (Mina_currency.Fee.to_uint64
                     constraint_constants.account_creation_fee) )
            ~valid_until:options.valid_until
            ~memo:options.memo
          |> Metadata_data.to_yojson
      ; suggested_fee =
          [ { suggested_fee with metadata = Some amount_metadata } ]
      }
  end

  module Real = Impl (Deferred.Result)
  module Mock = Impl (Result)
end

module Preprocess = struct
  module Metadata = struct
    type t = { valid_until : Unsigned_extended.UInt32.t option [@default None]; memo: string option [@default None] }
    [@@deriving yojson]

    let of_json r =
      of_yojson r
      |> Result.map_error ~f:(fun e ->
             Errors.create ~context:"Preprocess metadata of_json"
               (`Json_parse (Some e)))
  end

  module Env = struct
    module T (M : Monad_fail.S) = struct
      type t = { lift : 'a 'e. ('a, 'e) Result.t -> ('a, 'e) M.t }
    end

    module Real = T (Deferred.Result)
    module Mock = T (Result)

    let real : Real.t = { lift = Deferred.return }

    let mock : Mock.t = { lift = Fn.id }
  end

  module Impl (M : Monad_fail.S) = struct
    let lift_reason_validation_to_errors ~(env : Env.T(M).t) t =
      Result.map_error t ~f:(fun reasons ->
          Errors.create (`Operations_not_valid reasons))
      |> env.lift

    let handle ~(env : Env.T(M).t) (req : Construction_preprocess_request.t) =
      let open M.Let_syntax in
      let%bind metadata =
        match req.metadata with
        | Some json ->
            Metadata.of_json json |> env.lift |> M.map ~f:Option.return
        | None ->
            M.return None
      in
      let%bind partial_user_command =
        User_command_info.of_operations req.operations
        |> lift_reason_validation_to_errors ~env
      in
      let key (`Pk pk) =
        Public_key.Compressed.of_base58_check pk
        |> Result.map_error ~f:(fun _ ->
               Errors.create `Public_key_format_not_valid)
        |> env.lift
      in
      let%bind sender =
        key partial_user_command.User_command_info.Partial.source
      in
      let%map receiver =
        key partial_user_command.User_command_info.Partial.receiver
      in
      { Construction_preprocess_response.options =
          Some
            (Options.to_json
               { Options.sender
               ; token_id = partial_user_command.User_command_info.Partial.token
               ; receiver
               ; valid_until = Option.bind ~f:(fun m -> m.valid_until) metadata
               ; memo = Option.bind ~f:(fun m -> m.memo) metadata
               })
      ; required_public_keys = []
      }
  end

  module Real = Impl (Deferred.Result)
  module Mock = Impl (Result)
end

module Payloads = struct
  module Env = struct
    module T (M : Monad_fail.S) = struct
      type t = { lift : 'a 'e. ('a, 'e) Result.t -> ('a, 'e) M.t }
    end

    module Real = T (Deferred.Result)
    module Mock = T (Result)

    let real : Real.t = { lift = Deferred.return }

    let mock : Mock.t = { lift = Fn.id }
  end

  module Impl (M : Monad_fail.S) = struct
    let lift_reason_validation_to_errors ~(env : Env.T(M).t) t =
      Result.map_error t ~f:(fun reasons ->
          Errors.create (`Operations_not_valid reasons))
      |> env.lift

    let handle ~(env : Env.T(M).t) (req : Construction_payloads_request.t) =
      let open M.Let_syntax in
      let%bind metadata =
        match req.metadata with
        | Some json ->
            Metadata_data.of_json json |> env.lift
        | None ->
            M.fail
              (Errors.create
                 ~context:"Metadata is required for payloads request"
                 (`Json_parse None))
      in
      let%bind partial_user_command =
        User_command_info.of_operations ?valid_until:metadata.valid_until
        ?memo:metadata.memo
          req.operations
        |> lift_reason_validation_to_errors ~env
      in
      let%bind pk =
        let (`Pk pk) = partial_user_command.User_command_info.Partial.source in
        Public_key.Compressed.of_base58_check pk
        |> Result.map_error ~f:(fun _ ->
               Errors.create ~context:"compression" `Public_key_format_not_valid)
        |> Result.bind ~f:(fun pk ->
               Result.of_option (Public_key.decompress pk)
                 ~error:
                   (Errors.create ~context:"decompression"
                      `Public_key_format_not_valid))
        |> Result.map ~f:Rosetta_coding.Coding.of_public_key
        |> env.lift
      in
      let%bind user_command_payload =
        User_command_info.Partial.to_user_command_payload ~nonce:metadata.nonce
          partial_user_command
        |> env.lift
      in
      let random_oracle_input = Signed_command.to_input user_command_payload in
      let%map unsigned_transaction_string =
        { Transaction.Unsigned.random_oracle_input
        ; command = partial_user_command
        ; nonce = metadata.nonce
        }
        |> Transaction.Unsigned.render
        |> Result.map ~f:Transaction.Unsigned.Rendered.to_yojson
        |> Result.map ~f:Yojson.Safe.to_string
        |> env.lift
      in
      { Construction_payloads_response.unsigned_transaction =
          unsigned_transaction_string
      ; payloads =
          [ { Signing_payload.address = None
            ; account_identifier =
                Some
                  (User_command_info.account_id
                     partial_user_command.User_command_info.Partial.source
                     partial_user_command.User_command_info.Partial.token)
            ; hex_bytes = pk
            ; signature_type = Some "schnorr_poseidon"
            }
          ]
      }
  end

  module Real = Impl (Deferred.Result)
  module Mock = Impl (Result)
end

module Combine = struct
  module Env = struct
    module T (M : Monad_fail.S) = struct
      type t = { lift : 'a 'e. ('a, 'e) Result.t -> ('a, 'e) M.t }
    end

    module Real = T (Deferred.Result)
    module Mock = T (Result)

    let real : Real.t = { lift = Deferred.return }

    let mock : Mock.t = { lift = Fn.id }
  end

  module Impl (M : Monad_fail.S) = struct
    let handle ~(env : Env.T(M).t) (req : Construction_combine_request.t) =
      let open M.Let_syntax in
      let%bind json =
        try M.return (Yojson.Safe.from_string req.unsigned_transaction)
        with _ -> M.fail (Errors.create (`Json_parse None))
      in
      let%bind unsigned_transaction =
        Transaction.Unsigned.Rendered.of_yojson json
        |> Result.map_error ~f:(fun e -> Errors.create (`Json_parse (Some e)))
        |> Result.bind ~f:Transaction.Unsigned.of_rendered
        |> env.lift
      in
      (* TODO: validate that public key is correct w.r.t. signature for this transaction *)
      let%bind signature =
        match req.signatures with
        | s :: _ ->
            M.return @@ s.hex_bytes
        | _ ->
            M.fail (Errors.create `Signature_missing)
      in
      let signed_transaction_full =
        { Transaction.Signed.signature
        ; nonce = unsigned_transaction.nonce
        ; command = unsigned_transaction.command
        }
      in
      let%map rendered =
        Transaction.Signed.render signed_transaction_full |> env.lift
      in
      let signed_transaction =
        Transaction.Signed.Rendered.to_yojson rendered |> Yojson.Safe.to_string
      in
      { Construction_combine_response.signed_transaction }
  end

  module Real = Impl (Deferred.Result)
  module Mock = Impl (Result)
end

module Parse = struct
  module Env = struct
    module T (M : Monad_fail.S) = struct
      type t =
        { verify_payment_signature :
               network_identifier:Rosetta_models.Network_identifier.t
            -> payment:Transaction.Unsigned.Rendered.Payment.t
            -> signature:string
            -> unit
            -> (bool, Errors.t) M.t
        ; lift : 'a 'e. ('a, 'e) Result.t -> ('a, 'e) M.t
        }
    end

    module Real = T (Deferred.Result)
    module Mock = T (Result)

    let real : Real.t =
      { verify_payment_signature =
          (fun ~network_identifier ~payment ~signature () ->
            let open Deferred.Result in
            let open Deferred.Result.Let_syntax in
            let parse_pk ~which s =
              match Public_key.Compressed.of_base58_check s with
              | Ok pk ->
                  return pk
              | Error e ->
                  Deferred.Result.fail
                    (Errors.create
                       ~context:
                         (sprintf
                            "Parsing verify_payment_signature, bad %s public \
                             key"
                            which)
                       (`Json_parse (Some (Core_kernel.Error.to_string_hum e))))
            in
            let%bind source_pk = parse_pk ~which:"source" payment.from in
            let%bind receiver_pk = parse_pk ~which:"receiver" payment.to_ in
            let body =
              Signed_command_payload.Body.Payment
                { source_pk
                ; receiver_pk
                ; token_id = Mina_base.Token_id.of_uint64 payment.token
                ; amount = Mina_currency.Amount.of_uint64 payment.amount
                }
            in
            let fee_payer_pk = source_pk in
            let fee_token = Mina_base.Token_id.default in
            let fee = Mina_currency.Fee.of_uint64 payment.fee in
            let signer = fee_payer_pk in
            let valid_until =
              Option.map payment.valid_until
                ~f:Mina_numbers.Global_slot.of_uint32
            in
            let nonce = payment.nonce in
            let%map memo =
              match payment.memo with
              | None -> return User_command_info.Signed_command_memo.empty
              | Some str ->
                (match
                  User_command_info.Signed_command_memo.create_from_string str
                 with
                 | Error _ -> fail (Errors.create `Memo_invalid )
                 | Ok m -> return m)
            in
            let payload =
              Signed_command_payload.create ~fee ~fee_token ~fee_payer_pk ~nonce
                ~valid_until ~memo ~body
            in
            match Signature.Raw.decode signature with
            | None ->
                (* signature ill-formed, so invalid *)
                false
            | Some signature -> (
                (* choose signature verification based on network *)
                let signature_kind : Mina_signature_kind.t =
                  if String.equal network_identifier.network "mainnet" then
                    Mainnet
                  else Testnet
                in
                match
                  Signed_command.create_with_signature_checked ~signature_kind
                    signature signer payload
                with
                | None ->
                    (* invalid signature *)
                    false
                | Some _ ->
                    (* valid signature *)
                    true ))
      ; lift = Deferred.return
      }
  end

  module Impl (M : Monad_fail.S) = struct
    let handle ~(env : Env.T(M).t) (req : Construction_parse_request.t) =
      let open M.Let_syntax in
      let%bind json =
        try M.return (Yojson.Safe.from_string req.transaction)
        with _ -> M.fail (Errors.create (`Json_parse None))
      in
      let%map operations, account_identifier_signers, meta =
        let meta_of_command (cmd : User_command_info.Partial.t) =
          { Preprocess.Metadata.memo = cmd.memo
          ; valid_until = cmd.valid_until
          }
        in
        match req.signed with
        | true ->
            let%bind signed_rendered_transaction =
              Transaction.Signed.Rendered.of_yojson json
              |> Result.map_error ~f:(fun e ->
                     Errors.create (`Json_parse (Some e)))
              |> env.lift
            in
            let%bind signed_transaction =
              Transaction.Signed.of_rendered signed_rendered_transaction
              |> env.lift
            in
            let%map () =
              match signed_rendered_transaction.payment with
              | Some payment ->
                  (* Only perform signature validation on payments. *)
                  let%bind res =
                    env.verify_payment_signature
                      ~network_identifier:req.network_identifier ~payment
                      ~signature:signed_transaction.signature ()
                  in
                  if res then M.return ()
                  else M.fail (Errors.create `Signature_invalid)
              | None ->
                  M.return ()
            in
            ( User_command_info.to_operations ~failure_status:None
                signed_transaction.command
            , [ User_command_info.account_id signed_transaction.command.source
                  signed_transaction.command.token
              ]
            , meta_of_command signed_transaction.command)
        | false ->
            let%map unsigned_transaction =
              Transaction.Unsigned.Rendered.of_yojson json
              |> Result.map_error ~f:(fun e ->
                     Errors.create (`Json_parse (Some e)))
              |> Result.bind ~f:Transaction.Unsigned.of_rendered
              |> env.lift
            in
            ( User_command_info.to_operations ~failure_status:None
                unsigned_transaction.command
            , []
            , meta_of_command unsigned_transaction.command)
      in
      { Construction_parse_response.operations
      ; signers = []
      ; account_identifier_signers
      ; metadata =
        match (meta.memo, meta.valid_until) with
        | None, None -> None
        | _ -> Some (Preprocess.Metadata.to_yojson meta)
      }
  end

  module Real = Impl (Deferred.Result)
  module Mock = Impl (Result)
end

module Hash = struct
  module Env = struct
    module T (M : Monad_fail.S) = struct
      type t = { lift : 'a 'e. ('a, 'e) Result.t -> ('a, 'e) M.t }
    end

    module Real = T (Deferred.Result)
    module Mock = T (Result)

    let real : Real.t = { lift = Deferred.return }

    let mock : Mock.t = { lift = Fn.id }
  end

  module Impl (M : Monad_fail.S) = struct
    let handle ~(env : Env.T(M).t) (req : Construction_hash_request.t) =
      let open M.Let_syntax in
      let%bind json =
        try M.return (Yojson.Safe.from_string req.signed_transaction)
        with _ -> M.fail (Errors.create (`Json_parse None))
      in
      let%bind signed_transaction =
        Transaction.Signed.Rendered.of_yojson json
        |> Result.map_error ~f:(fun e -> Errors.create (`Json_parse (Some e)))
        |> Result.bind ~f:Transaction.Signed.of_rendered
        |> env.lift
      in
      let%bind signer =
        let (`Pk pk) = signed_transaction.command.source in
        Public_key.Compressed.of_base58_check pk
        |> Result.map_error ~f:(fun _ ->
               Errors.create ~context:"compression" `Public_key_format_not_valid)
        |> Result.bind ~f:(fun pk ->
               Result.of_option (Public_key.decompress pk)
                 ~error:
                   (Errors.create ~context:"decompression"
                      `Public_key_format_not_valid))
        |> Result.map_error ~f:(fun _ -> Errors.create `Malformed_public_key)
        |> env.lift
      in
      let%bind payload =
        User_command_info.Partial.to_user_command_payload
          ~nonce:signed_transaction.nonce signed_transaction.command
        |> env.lift
      in
      (* TODO: Implement signature coding *)
      let%map signature =
        Result.of_option
          (Signature.Raw.decode signed_transaction.signature)
          ~error:(Errors.create `Signature_missing)
        |> env.lift
      in
      let full_command = { Signed_command.Poly.payload; signature; signer } in
      let hash =
        Transaction_hash.hash_command (User_command.Signed_command full_command)
        |> Transaction_hash.to_base58_check
      in
      Transaction_identifier_response.create
        (Transaction_identifier.create hash)
  end

  module Real = Impl (Deferred.Result)
  module Mock = Impl (Result)
end

module Submit = struct
  module Env = struct
    module T (M : Monad_fail.S) = struct
      type ( 'gql_payment
           , 'gql_delegation
           , 'gql_create_token
           , 'gql_create_token_account
           , 'gql_mint_tokens )
           t =
        { gql_payment :
               payment:Transaction.Unsigned.Rendered.Payment.t
            -> signature:string
            -> unit
            -> ('gql_payment, Errors.t) M.t
              (* TODO: Validate network choice with separate query *)
        ; gql_delegation :
               delegation:Transaction.Unsigned.Rendered.Delegation.t
            -> signature:string
            -> unit
            -> ('gql_delegation, Errors.t) M.t
        ; gql_create_token :
               create_token:Transaction.Unsigned.Rendered.Create_token.t
            -> signature:string
            -> unit
            -> ('gql_create_token, Errors.t) M.t
        ; gql_create_token_account :
               create_token_account:
                 Transaction.Unsigned.Rendered.Create_token_account.t
            -> signature:string
            -> unit
            -> ('gql_create_token_account, Errors.t) M.t
        ; gql_mint_tokens :
               mint_tokens:Transaction.Unsigned.Rendered.Mint_tokens.t
            -> signature:string
            -> unit
            -> ('gql_mint_tokens, Errors.t) M.t
        ; lift : 'a 'e. ('a, 'e) Result.t -> ('a, 'e) M.t
        }
    end

    module Real = T (Deferred.Result)
    module Mock = T (Result)

    let real :
           graphql_uri:Uri.t
        -> ( 'gql_payment
           , 'gql_delegation
           , 'gql_create_token
           , 'gql_create_token_account
           , 'gql_mint_tokens )
           Real.t =
      let uint64 x = `String (Unsigned.UInt64.to_string x) in
      let uint32 x = `String (Unsigned.UInt32.to_string x) in
      let token_id x = `String (Mina_base.Token_id.to_string x) in
      fun ~graphql_uri ->
        { gql_payment =
            (fun ~payment ~signature () ->
              Graphql.query
                (Send_payment.make ~from:(`String payment.from)
                   ~to_:(`String payment.to_) ~token:(uint64 payment.token)
                   ~amount:(uint64 payment.amount) ~fee:(uint64 payment.fee)
                   ?validUntil:(Option.map ~f:uint32 payment.valid_until)
                   ?memo:payment.memo ~nonce:(uint32 payment.nonce) ~signature
                   ())
                graphql_uri)
        ; gql_delegation =
            (fun ~delegation ~signature () ->
              Graphql.query
                (Send_delegation.make ~sender:(`String delegation.delegator)
                   ~receiver:(`String delegation.new_delegate)
                   ~fee:
                     (uint64 delegation.fee)
                   (* TODO: Enable these when graphql supports sending validUntil for these transactions *)
                   (* ?validUntil:(Option.map ~f:uint32 delegation.valid_until) *)
                   ?memo:delegation.memo ~nonce:(uint32 delegation.nonce)
                   ~signature ())
                graphql_uri)
        ; gql_create_token =
            (fun ~create_token ~signature () ->
              Graphql.query
                (Send_create_token.make
                   ~receiver:(`String create_token.receiver)
                   (* ?validUntil:(Option.map ~f:uint32 create_token.valid_until) *)
                   ~fee:(uint64 create_token.fee) ?memo:create_token.memo
                   ~nonce:(uint32 create_token.nonce)
                   ~signature ())
                graphql_uri)
        ; gql_create_token_account =
            (fun ~create_token_account ~signature () ->
              Graphql.query
                (Send_create_token_account.make
                   ~tokenOwner:(`String create_token_account.token_owner)
                   (* ?validUntil:(Option.map ~f:uint32 create_token_account.valid_until) *)
                   ~receiver:(`String create_token_account.receiver)
                   ~token:(token_id create_token_account.token)
                   ~fee:(uint64 create_token_account.fee)
                   ?memo:create_token_account.memo
                   ~nonce:(uint32 create_token_account.nonce)
                   ~signature ())
                graphql_uri)
        ; gql_mint_tokens =
            (fun ~mint_tokens ~signature () ->
              Graphql.query
                (Send_mint_tokens.make ~sender:(`String mint_tokens.token_owner)
                   (* ?validUntil:(Option.map ~f:uint32 mint_tokens.valid_until) *)
                   ~receiver:(`String mint_tokens.receiver)
                   ~token:(token_id mint_tokens.token)
                   ~amount:(uint64 mint_tokens.amount)
                   ~fee:(uint64 mint_tokens.fee) ?memo:mint_tokens.memo
                   ~nonce:(uint32 mint_tokens.nonce) ~signature ())
                graphql_uri)
        ; lift = Deferred.return
        }
  end

  module Impl (M : Monad_fail.S) = struct
    let handle
        ~(env :
           ( 'gql_payment
           , 'gql_delegation
           , 'gql_create_token
           , 'gql_create_token_account
           , 'gql_mint_tokens )
           Env.T(M).t) (req : Construction_submit_request.t) =
      let open M.Let_syntax in
      let%bind json =
        try M.return (Yojson.Safe.from_string req.signed_transaction)
        with _ -> M.fail (Errors.create (`Json_parse None))
      in
      let%bind signed_transaction =
        Transaction.Signed.Rendered.of_yojson json
        |> Result.map_error ~f:(fun e -> Errors.create (`Json_parse (Some e)))
        |> env.lift
      in
      let open M.Let_syntax in
      let%map hash =
        match
          ( signed_transaction.payment
          , signed_transaction.stake_delegation
          , signed_transaction.create_token
          , signed_transaction.create_token_account
          , signed_transaction.mint_tokens )
        with
        | Some payment, None, None, None, None ->
            let%map res =
              env.gql_payment ~payment ~signature:signed_transaction.signature
                ()
            in
            let (`UserCommand payment) = res#sendPayment#payment in
            payment#hash
        | None, Some delegation, None, None, None ->
            let%map res =
              env.gql_delegation ~delegation
                ~signature:signed_transaction.signature ()
            in
            let (`UserCommand delegation) = res#sendDelegation#delegation in
            delegation#hash
        | None, None, Some create_token, None, None ->
            let%map res =
              env.gql_create_token ~create_token
                ~signature:signed_transaction.signature ()
            in
            res#createToken#createNewToken#hash
        | None, None, None, Some create_token_account, None ->
            let%map res =
              env.gql_create_token_account ~create_token_account
                ~signature:signed_transaction.signature ()
            in
            res#createTokenAccount#createNewTokenAccount#hash
        | None, None, None, None, Some mint_tokens ->
            let%map res =
              env.gql_mint_tokens ~mint_tokens
                ~signature:signed_transaction.signature ()
            in
            res#mintTokens#mintTokens#hash
        | _ ->
            M.fail
              (Errors.create
                 ~context:
                   "Must have one of payment, stakeDelegation, createToken, \
                    createTokenAccount, or mintTokens"
                 (`Json_parse None))
      in
      Transaction_identifier_response.create
        (Transaction_identifier.create hash)
  end

  module Real = Impl (Deferred.Result)
  module Mock = Impl (Result)
end

let router ~get_graphql_uri_or_error ~logger (route : string list) body =
  [%log debug] "Handling /construction/ $route"
    ~metadata:[ ("route", `List (List.map route ~f:(fun s -> `String s))) ] ;
  let open Deferred.Result.Let_syntax in
  match route with
  | [ "derive" ] ->
      let%bind req =
        Errors.Lift.parse ~context:"Request"
        @@ Construction_derive_request.of_yojson body
        |> Errors.Lift.wrap
      in
      let%map res =
        Derive.Real.handle ~env:Derive.Env.real req |> Errors.Lift.wrap
      in
      Construction_derive_response.to_yojson res
  | [ "preprocess" ] ->
      let%bind req =
        Errors.Lift.parse ~context:"Request"
        @@ Construction_preprocess_request.of_yojson body
        |> Errors.Lift.wrap
      in
      let%map res =
        Preprocess.Real.handle ~env:Preprocess.Env.real req |> Errors.Lift.wrap
      in
      Construction_preprocess_response.to_yojson res
  | [ "metadata" ] ->
      let%bind req =
        Errors.Lift.parse ~context:"Request"
        @@ Construction_metadata_request.of_yojson body
        |> Errors.Lift.wrap
      in
      let%bind graphql_uri = get_graphql_uri_or_error () in
      let%map res =
        Metadata.Real.handle ~graphql_uri
          ~env:(Metadata.Env.real ~graphql_uri)
          req
        |> Errors.Lift.wrap
      in
      Construction_metadata_response.to_yojson res
  | [ "payloads" ] ->
      let%bind req =
        Errors.Lift.parse ~context:"Request"
        @@ Construction_payloads_request.of_yojson body
        |> Errors.Lift.wrap
      in
      let%map res =
        Payloads.Real.handle ~env:Payloads.Env.real req |> Errors.Lift.wrap
      in
      Construction_payloads_response.to_yojson res
  | [ "combine" ] ->
      let%bind req =
        Errors.Lift.parse ~context:"Request"
        @@ Construction_combine_request.of_yojson body
        |> Errors.Lift.wrap
      in
      let%map res =
        Combine.Real.handle ~env:Combine.Env.real req |> Errors.Lift.wrap
      in
      Construction_combine_response.to_yojson res
  | [ "parse" ] ->
      let%bind req =
        Errors.Lift.parse ~context:"Request"
        @@ Construction_parse_request.of_yojson body
        |> Errors.Lift.wrap
      in
      let%map res =
        Parse.Real.handle ~env:Parse.Env.real req |> Errors.Lift.wrap
      in
      Construction_parse_response.to_yojson res
  | [ "hash" ] ->
      let%bind req =
        Errors.Lift.parse ~context:"Request"
        @@ Construction_hash_request.of_yojson body
        |> Errors.Lift.wrap
      in
      let%map res =
        Hash.Real.handle ~env:Hash.Env.real req |> Errors.Lift.wrap
      in
      Transaction_identifier_response.to_yojson res
  | [ "submit" ] ->
      let%bind req =
        Errors.Lift.parse ~context:"Request"
        @@ Construction_submit_request.of_yojson body
        |> Errors.Lift.wrap
      in
      let%bind graphql_uri = get_graphql_uri_or_error () in
      let%map res =
        Submit.Real.handle ~env:(Submit.Env.real ~graphql_uri) req
        |> Errors.Lift.wrap
      in
      Transaction_identifier_response.to_yojson res
  | _ ->
      Deferred.Result.fail `Page_not_found
