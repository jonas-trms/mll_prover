(*Types*)
type formula = A of int | NA of int | P of formula * formula | T of formula * formula

type sequent = formula list

type permutation = int array

type proof = 
  | Atom1 of int
  | Atom2 of int
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

(*Working on proofs*)
let aux_par seq i =
  let rec aux_par1 seq acc = 
    match seq, acc with
    | x::y::ys, 1 -> P(x, y)::ys
    | x::ys, i when i > 1 -> x::(aux_par1 ys (i-1))
    | _ -> failwith "Bad construction" in
  aux_par1 seq i

let aux_unpar seq i =
  let rec aux_par1 seq acc = 
    match seq, acc with
    | P(x, y)::ys, 1 -> x::y::ys
    | x::ys, i when i > 1 -> x::(aux_par1 ys (i-1))
    | _ -> failwith "Bad construction" in
  aux_par1 seq i

let aux_tensor seq1 seq2 =
match List.rev seq1, seq2 with
| x::xs, y::ys -> (List.rev xs) @ (T(x, y)::ys)
| _, _ -> failwith "Bad construction"

let aux_perm seq sigma =
if List.length seq <> Array.length sigma then
  failwith "Bad construction"
else begin
  let m = Array.length sigma in
  let tab_ant = Array.of_list seq in
  let tab_img = Array.make m (A (-1)) in

  for i = 0 to m-1 do
    let j = sigma.(i) in
    if j < 1 || j > m then failwith "Bad construction"
    else tab_img.(j-1) <- tab_ant.(i)
  done;

  for i = 0 to m-1 do
    if tab_img.(i) = A (-1) then failwith "Bad construction"
  done;

  Array.to_list tab_img
end

let rec get_seq = function
| Atom1 i -> [A i; NA i]
| Atom2 i -> [NA i; A i]
| Par (i, p) -> aux_par (get_seq p) i
| Tensor (p1, p2) -> aux_tensor (get_seq p1) (get_seq p2)
| Permutation (sigma, p) -> aux_perm (get_seq p) sigma

(*Printing*)
let rec print_formula = function
  | A (i) -> Printf.printf "(A %d)" i
  | NA (i) -> Printf.printf "(NA %d)" i
  | P (f1, f2) -> print_string "("; print_formula f1; print_string ") & ("; print_formula f2; print_string ")"
  | T (f1, f2) -> print_string "("; print_formula f1; print_string ") X ("; print_formula f2; print_string ")"

let rec print_seq = function
  | [] -> ()
  | x::xs -> print_formula x; print_string ", "; print_seq xs

let rec print_permutation sigma = 
  for i = 0 to Array.length sigma - 1 do
    Printf.printf "%d " sigma.(i)
  done

let rec print_proof p =
  print_seq (get_seq p);
  print_newline ();
  match p with
  | Atom1 _ | Atom2 _ -> ()
  | Par (i,  p1) -> Printf.printf "Par %d \n" i; print_proof p1
  | Tensor (p1, p2) -> print_string "Tensor \nLeft begins\n"; print_proof p1; print_string "Left ends\nRight begins\n"; print_proof p2; print_string "Right ends\n";
  | Permutation (sigma, p) -> print_string "Permutation\n"; print_permutation sigma; print_newline (); print_proof p

let print_add ((n, w) : address) = 
  let rec print_dir = function
  | [] -> ()
  | Right::xs -> print_string "r"; print_dir xs
  | Left::xs -> print_string "l"; print_dir xs in
  print_int n; print_dir w

let print_rep (t, s) = 
  let rec print_tree = function
    | F(add1, add2) -> print_string "F "; print_add add1; print_string " "; print_add add2; print_newline ()
    | N_P(add, t) -> print_string "P "; print_add add; print_newline (); print_tree t
    | N_T(add, t1, t2) -> print_string "T "; print_add add;
                          print_string "\nLeft begins\n"; print_tree t1; print_string "Left ends\nRight begins\n"; print_tree t2; print_string "Right ends\n"

  in print_seq s; print_newline(); print_tree t 

(*Encoding*)
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

let add_sort add1 add2 = 
  if add_cmp add1 add2 <= 0 then add1, add2
  else add2, add1

let rec map_psi psi n rep = 
  match rep with
  | F(add1, add2) -> let a, b = add_sort (psi n add1) (psi n add2) in F(a, b)
  | N_T(add, t1, t2) -> N_T(psi n add, map_psi psi n t1, map_psi psi n t2)
  | N_P(add, t) -> N_P(psi n add, map_psi psi n t)

let psi_1 n = function
  | (i, w) when i = n -> (n, Left::w)
  | (i, w) when i = n+1 -> (n, Right::w)
  | (i, w) when i > n+1 -> (i-1, w)
  | (i, w) -> (i, w)

let psi_2 n = function
  | (i, w) when i = n -> (n, Left::w) 
  | (i, w) -> (i, w)

let psi_3 n = function
  | (1, w) -> (n, Right::w)
  | (i, w) -> (n + i - 1, w)

let add_sigma sigma = function
  | n, w -> sigma.(n-1), w

let rec map_sigma sigma rep = 
    match rep with
    | F(add1, add2) -> let a, b = add_sort (add_sigma sigma add1) (add_sigma sigma add2) in F(a, b)
    | N_T(add, t1, t2) -> N_T(add_sigma sigma add, map_sigma sigma t1, map_sigma sigma t2)
    | N_P(add, t) -> N_P(add_sigma sigma add, map_sigma sigma t)

let encode proof =
  let rec encode_aux = function
  | Atom1(i) -> F((1, []), (2, []))
  | Atom2(i) -> F((1, []), (2, []))
  | Par(n, p) -> N_P((n, []), 
                      map_psi psi_1 n (encode_aux p))
  | Tensor(p1, p2) -> let n = List.length (get_seq p1) in 
                      N_T((n, []), 
                          map_psi psi_2 n (encode_aux p1),
                          map_psi psi_3 n (encode_aux p2))
  | Permutation(sigma, p) -> map_sigma sigma (encode_aux p) in

  (encode_aux proof, get_seq proof)

(*Decode*)
let psi_1_inv n = function
  | (i, Left::w) when i = n -> (n, w)
  | (i, Right::w) when i = n -> (n+1, w)
  | (i, w) when i > n -> (i+1, w)
  | (i, w) -> (i, w)

let rec decode (t, s) = 
  match t with
  | F(_, _) -> begin
    match s with
    | [A(i); NA(j)] when i = j -> Atom1(i)
    | [NA(i); A(j)] when i = j -> Atom2(i)
    | _ -> failwith "Bad construction"
    end
  | N_P((n, w), t0) -> Par(n, decode ((map_psi psi_1_inv n t0), aux_unpar s n)) 
  | N_T(_, _, _) -> failwith "Not implemented"

(*Main*)
(* let proof_1 = Par(2, Permutation([|2; 1; 3; 4|], Tensor(Atom1(1), Permutation ([|3; 1; 2|], Tensor (Atom2(2), Atom2(3))))));;

let () = print_proof proof_1; print_newline();;

let () = print_rep (encode proof_1); print_newline();; *)

let proof_2 = Par(1, Permutation([|2; 1|], Atom2(1)));;

let () = print_proof proof_2; print_newline();;

let () = print_rep (encode proof_2); print_newline();;

let () = print_proof (decode (encode proof_2));;