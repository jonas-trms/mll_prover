(*Types*)
type formula = A of int | NA of int | P of formula * formula | T of formula * formula

type sequent = formula list

type permutation = int array

type proof = 
  | Axiom of int
  | Par of int * proof
  | Tensor of proof * proof
  | Permutation of permutation * proof

type dir =
  | Left
  | Right

type address = int * dir list

type tree = 
  | F of address * address
  | N_P of address * tree
  | N_T of address * tree * tree
  
type representation = tree * sequent


(*Manipulating sequents*)
(*Merge formulas i and i+1 into a par*)
let rec aux_par seq i =
  match seq, i with
  | x::y::ys, 1 -> P(x, y)::ys
  | x::ys, i when i > 1 -> x::(aux_par ys (i-1))
  | _ -> failwith "Bad construction aux_par"

(*Split the ith formula, supposing it's a par*)
let rec aux_unpar seq i =
  match seq, i with
  | P(x, y)::ys, 1 -> x::y::ys
  | x::ys, i when i > 1 -> x::(aux_unpar ys (i-1))
  | _ -> failwith "Bad construction"

(*Merge two sequents using the tensor rule*)
let aux_tensor seq1 seq2 =
  match List.rev seq1, seq2 with
  | x::xs, y::ys -> (List.rev xs) @ (T(x, y)::ys)
  | _, _ -> failwith "Bad construction aux_tensor"

(*Apply a permutation to a sequent*)
let aux_perm seq sigma =
  let m = Array.length sigma in
  if List.length seq <> m then failwith "Bad construction aux_perm1"
  else begin
    let tab_ant = Array.of_list seq in
    let tab_img = Array.make m (A (-1)) in

    for i = 0 to m-1 do
      let j = sigma.(i) in
      if j < 1 || j > m then failwith "Bad construction aux_perm2"
      else tab_img.(j-1) <- tab_ant.(i)
    done;

    for i = 0 to m-1 do
      if tab_img.(i) = A (-1) then failwith "Bad construction aux_perm3"
    done;

    Array.to_list tab_img
  end

(*Calculate the sequent linked to a proof*)
let rec get_seq = function
  | Axiom i -> [NA i; A i]
  | Par (i, p) -> aux_par (get_seq p) i
  | Tensor (p1, p2) -> aux_tensor (get_seq p1) (get_seq p2)
  | Permutation (sigma, p) -> aux_perm (get_seq p) sigma


(*Printing*)
let rec print_formula = function
  | A i -> Printf.printf "%d" i
  | NA i -> Printf.printf "%d^" i
  | P (f1, f2) -> print_string "("; print_formula f1; print_string ") | ("; print_formula f2; print_string ")"
  | T (f1, f2) -> print_string "("; print_formula f1; print_string ") * ("; print_formula f2; print_string ")"

let rec print_seq = function
  | [] -> ()
  | [x] -> print_formula x
  | x::xs -> print_formula x; print_string ", "; print_seq xs

let print_permutation sigma =
  for i = 0 to Array.length sigma - 1 do
    Printf.printf "%d " sigma.(i)
  done

let rec print_proof p =
  print_seq (get_seq p);
  print_newline ();
  match p with
  | Axiom _ -> ()
  | Par (i, p1) -> Printf.printf "Par %d \n" i; print_proof p1
  | Tensor (p1, p2) -> print_string "Tensor \nLeft begins\n"; print_proof p1; print_string "Left ends\nRight begins\n"; print_proof p2; print_string "Right ends\n";
  | Permutation (sigma, p) -> print_string "Permutation\n"; print_permutation sigma; print_newline (); print_proof p

(*Print an address*)
let print_add ((n, w) : address) = 
  let rec print_dir = function
    | [] -> ()
    | Right::xs -> print_string "r"; print_dir xs
    | Left::xs -> print_string "l"; print_dir xs in
  print_int n; print_dir w

(*Print a representation*)
let print_rep (t, s) = 
  let rec print_tree = function
    | F (add1, add2) -> print_string "F "; print_add add1; print_string " "; print_add add2; print_newline ()
    | N_P (add, t) -> print_string "P "; print_add add; print_newline (); print_tree t
    | N_T (add, t1, t2) -> print_string "T "; print_add add;
                           print_string "\nLeft begins\n"; print_tree t1; print_string "Left ends\nRight begins\n"; print_tree t2; print_string "Right ends\n"
  in print_seq s; print_newline(); print_tree t 


(*Encoding*)
(*Define an order on addresses*)
let add_cmp add1 add2 = 
  (*Left < Right*)
  let rec dir_cmp d1 d2 = 
    match d1, d2 with
    | [], [] -> 0
    | [], _ -> -1
    | _, [] -> 1
    | Left::xs, Right::ys -> -1
    | Right::xs, Left::ys -> 1
    | _::xs, _::ys -> dir_cmp xs ys in
  match add1, add2 with
  | (n1, add1), (n2, add2) when n1 < n2 -> -1
  | (n1, add1), (n2, add2) when n1 > n2 -> 1
  | (n1, add1), (n2, add2) -> dir_cmp add1 add2

(*Sort two addresses*)
let add_sort add1 add2 = 
  if add_cmp add1 add2 <= 0 then add1, add2
  else add2, add1

(*Given a function manipulating indexes, map it to a representation*)
let rec map_psi psi = function
  | F (add1, add2) -> let a, b = add_sort (psi add1) (psi add2) in F(a, b)
  | N_T (add, t1, t2) -> N_T (psi add, map_psi psi t1, map_psi psi t2)
  | N_P (add, t) -> N_P (psi add, map_psi psi t)

(*Reindexing functions used for the encoding*)
(*In case of a par*)
let psi_1 n = function
  | (i, w) when i = n -> (n, Left::w)
  | (i, w) when i = n+1 -> (n, Right::w)
  | (i, w) when i > n+1 -> (i-1, w)
  | (i, w) -> (i, w)

(*In case of a tensor*)
let psi_2 n = function
  | (i, w) when i = n -> (n, Left::w)
  | (i, w) when i > n+1 -> failwith "index out of scope in psi_2"
  | (i, w) -> (i, w)

let psi_3 n = function
  | (1, w) -> (n, Right::w)
  | (i, w) -> (n + i - 1, w)

(*Given a permutation, map it to a representation*)
let add_sigma sigma = function
  | n, w -> sigma.(n-1), w

let rec map_sigma sigma = function
  | F (add1, add2) -> let a, b = add_sort (add_sigma sigma add1) (add_sigma sigma add2) in F (a, b)
  | N_T (add, t1, t2) -> N_T (add_sigma sigma add, map_sigma sigma t1, map_sigma sigma t2)
  | N_P (add, t) -> N_P (add_sigma sigma add, map_sigma sigma t)

let encode proof =
  let rec encode_aux = function
  | Axiom i -> F((1, []), (2, []))
  | Par (n, p) -> N_P ((n, []),
                       map_psi (psi_1 n) (encode_aux p))
  | Tensor (p1, p2) -> let n = List.length (get_seq p1) in
                       N_T ((n, []),
                            map_psi (psi_2 n) (encode_aux p1),
                            map_psi (psi_3 n) (encode_aux p2))
  | Permutation (sigma, p) -> map_sigma sigma (encode_aux p) in
  (encode_aux proof, get_seq proof)


(*Decoding*)
(*Given a tree, extract the sorted indexes of its root addresses*)
let list_of_roots t =
  let rec aux = function
    | F ((n1, []), (n2, [])) -> [n1; n2]
    | F ((n1, []), _) -> [n1]
    | F (_, (n2, [])) -> [n2]
    | F (_, _) -> []

    | N_P ((n, []), t1) -> n::(aux t1)
    | N_P (_, t1) -> aux t1

    | N_T ((n, []), t1, t2) -> n::(aux t1)@(aux t2)
    | N_T (_, t1, t2) -> (aux t1)@(aux t2) in
  List.sort (fun x y -> x - y) (aux t)

(*Given the two subsets G and D of a shuffle G><D, merge them into their concatenation G.D*)
let sigma_merge sigma1 sigma2 n =
  let m1 = Array.length sigma1 in
  let m2 = Array.length sigma2 in
  let merged = Array.make (m1 + m2 + 1) (-1) in

  for i = 0 to m1-1 do
    if sigma1.(i) < 1 || sigma1.(i) > m1 + m2 + 1 then failwith "Bad construction1"
    else merged.(sigma1.(i) - 1) <- i + 1
  done;
  
  for i = 0 to m2-1 do
    if sigma2.(i) < 1 || sigma2.(i) > m1 + m2 + 1 then failwith "Bad construction2"
    else merged.(sigma2.(i) - 1) <- m1 + i + 1
  done;

  for i = 0 to m1 + m2 do
    if (i + 1) <> n && merged.(i) = -1 then failwith "Bad construction3"
  done;

  merged

(*Given a sequent, the concatenation G.D, n and |G|, build G,A and B,D*)
let seq_split s merged n m1 =
  let m = List.length s in
  let rec aux s gamma delta acc =
    match s with
    | [] when acc = m+1 -> (gamma, delta)
    | [] -> Printf.printf "wrong acc %d\n" acc; failwith "Bad construction4"
    | x::xs when acc = n -> aux xs gamma delta (acc+1)
    | x::xs -> if merged.(acc-1) < m1+1 then aux xs (x::gamma) delta (acc+1)
               else aux xs gamma (x::delta) (acc+1) in

  let gamma, delta = aux s [] [] 1 in
  let f1, f2 =
     match List.nth s (n-1) with
     | T(x, y) -> (x, y)
     | _ -> failwith "Bad construction for tensor" in
  List.rev (f1::gamma), f2::(List.rev delta)

(*Given the subsets G, D and n, build the permutation from (G, A*B, D) to the initial set*)
let get_perm sigma1 sigma2 n = 
  let m1, m2 = Array.length sigma1, Array.length sigma2 in
  let perm = Array.make (m1 + m2 + 1) (-1) in
  for i = 0 to m1 - 1 do
    perm.(i) <- sigma1.(i)
  done;

  perm.(m1) <- n;

  for i = 0 to m2 - 1 do
    perm.(m1 + i + 1) <- sigma2.(i)
  done;

  perm

(*Reindexing functions used for the decoding*)
(*In case of a par*)
let psi_1_merged n = function
  | (i, Left::w) when i = n -> (n, w)
  | (i, Right::w) when i = n -> (n+1, w)
  | (i, w) when i > n -> (i+1, w)
  | (i, w) -> (i, w)

(*In case of a tensor*)
(*m1 corresponds to |G|*)
let alpha_1 merged m1 n = function
  | (i, Left::w) when i = n -> (m1 + 1, w)
  | (i, w) when i <> n -> (merged.(i-1), w)
  | _ -> failwith "Bad construction"

let alpha_2 merged m1 n = function
  | (i, Right::w) when i = n -> (1, w)
  | (i, w) when i <> n -> (merged.(i-1) - m1 + 1, w)
  | _ -> failwith "Bad construction"

let rec decode (t, s) =
  match t with
  | F ((1, []), (2, [])) -> begin
    match s with
    | [A i; NA j] when i = j -> Permutation ([|2; 1|], Axiom i)
    | [NA i; A j] when i = j -> Axiom i
    | _ -> print_seq s; print_newline (); failwith "Bad construction: not an axiom"
    end
  | F (_, _) -> failwith "Bad construction: wrong addresses in axiom"
  | N_P ((n, w), t0) -> Par(n, decode (map_psi (psi_1_merged n) t0, aux_unpar s n))
  | N_T ((n, w), t1, t2) ->
      let sigma1 = Array.of_list (list_of_roots t1) in
      let m1 = Array.length sigma1 in
      let sigma2 = Array.of_list (list_of_roots t2) in

      let merged = sigma_merge sigma1 sigma2 n in

      let s1, s2 = seq_split s merged n m1 in
      let t1_map, t2_map = map_psi (alpha_1 merged m1 n) t1, map_psi (alpha_2 merged m1 n) t2 in
      let p1, p2 = decode (t1_map, s1), decode (t2_map, s2) in
      Permutation (get_perm sigma1 sigma2 n, Tensor (p1, p2))

    
(*Examples*)
let proof_1 = Par (2, Permutation([|2; 1; 3; 4|], Tensor (Permutation ([|2; 1|], Axiom 1), Permutation ([|3; 1; 2|], Tensor (Axiom 2, Axiom 3)))));;

let proof_2 = Tensor (Permutation ([|2; 1|], Axiom 1), Permutation ([|3; 1; 2|], Tensor (Axiom 2, Axiom 3)));;

let proof_3 = Permutation ([|3;2;1;4|], Tensor (Permutation ([|2; 1|], Axiom 1), Permutation([|2;1;3|], Tensor (Axiom 2, Axiom 3))));;

let proof_4 = Permutation ([|1;6;2;3;4;5|],
                          Tensor (Permutation ([|2; 1|], Axiom 1),
                                Permutation ([|2;1;3;4;5|],
                                            Tensor (Permutation ([|2; 1|], Axiom 2),
                                                    Permutation([|2; 1; 4; 3|], 
                                                                Tensor (Permutation ([|2; 1|], Axiom 3),
                                                                        Permutation([|3;1;2|], 
                                                                                    Tensor(Permutation ([|2; 1|], Axiom 4),
                                                                                    Axiom 5))))))));;

let a = proof_4;;
print_proof a; print_newline();print_newline();
print_rep (encode a); print_newline();print_newline();
print_proof (decode (encode a)); print_newline(); print_newline();;
print_rep (encode (decode (encode a))); print_newline();print_newline();
