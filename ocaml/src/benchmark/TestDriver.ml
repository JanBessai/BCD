open Printf
open List
open Array
open BCD
open OcamlTy.T
open SubtypeRelation
open Core_bench.Std

let worstCase n =
  let rec arr = Array.init n (fun x -> x)
  and makeLeftType s n = Inter (Arr (Var n, Var n), s)  
  and makeRightType s m = 
    let sigma = Array.fold_left (fun s n -> if n <> m then Inter (Var(n), s) else s) Omega arr in
    Inter(Arr(sigma, sigma), s)
  in
  Array.fold_left (fun (l, r) n -> (makeLeftType l n, makeRightType r n)) (Omega, Omega) arr

let rec to_string ty =
  match ty with
    | Omega -> "ω"
    | Var(n) -> sprintf "%d" n
    | Arr(s, t) -> sprintf "( %s → %s )" (to_string s) (to_string t)
    | Inter(s, t) -> sprintf "%s ∩ %s" (to_string s) (to_string t)

let rec ty_size ty =
  match ty with
    | Omega -> 1
    | Var(_) -> 1
    | Arr(s, t) -> 1 + ty_size s + ty_size t
    | Inter(s, t) -> 1 + ty_size s + ty_size t

let worstCaseTest = 
  let (x, y) = worstCase 200 in
  let foo = printf "%d %d\n" (ty_size x) (ty_size y) in
  Bench.Test.create ~name:(sprintf "worstcase %d" (ty_size y)) (fun () -> coq_Subtype_decidable x y)

open Core
let () =
  Command.run (Bench.make_command [worstCaseTest])
