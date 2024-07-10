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

type address_tree = dir list

type node_type = Leaf | Unary | Binary

type tree = 
  | Unknown
  | F of address * address
  | U of address * tree
  | B of address * tree * tree
  
type representation = tree * sequent

(*Exceptions*)
exception NotDual
exception MandatoryNotUsed
exception ToName

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

let rec print_formula_latex = function
  | A i -> Printf.printf "X_%d" i
  | NA i -> Printf.printf "{X_%d}\\orth" i
  | P (f1, f2) -> print_string "("; print_formula_latex f1; print_string ") \\parr ("; print_formula_latex f2; print_string ")"
  | T (f1, f2) -> print_string "("; print_formula_latex f1; print_string ") \\tensor ("; print_formula_latex f2; print_string ")"

let rec print_list p = function
  | [] -> ()
  | [x] -> p x
  | x::xs -> p x; print_string ", "; print_list p xs

let print_int_list = print_list print_int

let print_seq = print_list print_formula

let print_seq_latex = print_list print_formula_latex

let print_seq_low s s' =
  let print_pair x y =
    (if y then print_string "<" else ()); print_formula x; (if y then print_string ">" else ()) in
  let rec aux s s' =
    match s, s' with
    | [], [] -> ()
    | [x], [y] -> print_pair x y
    | x::xs, y::ys -> print_pair x y; print_string ", "; aux xs ys
    | _ -> failwith "Bad construction print_seq_low"
  in aux s (Array.to_list s')

let print_seq_low_latex s s' =
  let print_pair x y =
    (if y then print_string "\\boldsymbol{" else ()); print_formula_latex x; (if y then print_string "}" else ()) in
  let rec aux s s' =
    match s, s' with
    | [], [] -> ()
    | [x], [y] -> print_pair x y
    | x::xs, y::ys -> print_pair x y; print_string ", "; aux xs ys
    | _ -> failwith "Bad construction print_seq_low"
  in aux s (Array.to_list s')


let print_permutation sigma =
  for i = 0 to Array.length sigma - 1 do
    Printf.printf "%d " sigma.(i)
  done

let rec repeat_string s n =
  if n = 0 then "" else s ^ repeat_string s (n - 1)

let space = "   "

let print_proof p =
  let rec aux p_curr depth =
    Printf.printf "%s" (repeat_string space depth); print_seq (get_seq p_curr);
    print_newline ();
    match p_curr with
    | Axiom _ -> ()
    | Par (i, p1) -> Printf.printf "%sPar %d \n" (repeat_string space depth) i; aux p1 depth
    | Tensor (p1, p2) -> aux p2 (depth + 1); Printf.printf "%sTensor \n" (repeat_string space depth); aux p1 (depth + 1);
    | Permutation (sigma, p1) -> Printf.printf "%sPermutation : " (repeat_string space depth);
                                 print_permutation sigma; print_newline (); aux p1 depth in
  aux p 0

let print_proof_latex p =
  let rec aux p_curr depth =
    let s_curr = get_seq p_curr in 
    match p_curr with
    | Axiom _ -> Printf.printf "%s\\axv{" (repeat_string space depth); print_seq_latex s_curr; print_string "}"
    | Par(_, p1) -> aux p1 (depth + 1); print_newline(); 
                    Printf.printf "%s\\parrv{" (repeat_string space depth); print_seq_latex s_curr; print_string "}"
    | Tensor(p1, p2) -> aux p1 (depth + 1); print_newline (); print_newline ();
                        aux p2 (depth + 1); print_newline ();
                        Printf.printf "%s\\tensorv{" (repeat_string space depth); print_seq_latex s_curr; print_string "}"
    | Permutation(sigma, p1) -> aux p1 depth; print_newline ();
                                Printf.printf"%s\\permv{\\someperm}{\\permapp{\\someperm}{" (repeat_string space depth); print_seq_latex s_curr; print_string "}}" in
  Printf.printf "\\begin{prooftree}\n";                           
  aux p 0;
  Printf.printf "\n\\end{prooftree}\n"

(*Print an address*)
let print_add ((n, w) : address) = 
  let rec print_dir = function
    | [] -> ()
    | Right::xs -> print_string "r"; print_dir xs
    | Left::xs -> print_string "l"; print_dir xs in
  print_int n; print_dir w

(*Print a mapping*)
let print_mapping m =
  for i = 0 to (Array.length m) - 1 do
    print_add m.(i); print_string " "
  done

(*Print a representation*)
let print_rep (t, s) = 
  let rec print_tree t depth = match t with
  | Unknown -> Printf.printf "%s?\n" (repeat_string space depth);
  | F (add1, add2) -> Printf.printf "%sF " (repeat_string space depth); print_add add1; print_string " "; print_add add2; print_newline ()
  | U (add, t) -> Printf.printf "%sU " (repeat_string space depth); print_add add; print_newline (); print_tree t depth
  | B (add, t1, t2) -> print_tree t2 (depth + 1); Printf.printf "%sB " (repeat_string space depth); print_add add; print_newline(); print_tree t1 (depth + 1);
  in print_tree t 0; print_newline(); print_seq s; print_newline ()


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
  | Unknown -> Unknown
  | F (add1, add2) -> let a, b = add_sort (psi add1) (psi add2) in F(a, b)
  | B (add, t1, t2) -> B (psi add, map_psi psi t1, map_psi psi t2)
  | U (add, t) -> U (psi add, map_psi psi t)

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
  | Unknown -> Unknown
  | F (add1, add2) -> let a, b = add_sort (add_sigma sigma add1) (add_sigma sigma add2) in F (a, b)
  | B (add, t1, t2) -> B (add_sigma sigma add, map_sigma sigma t1, map_sigma sigma t2)
  | U (add, t) -> U (add_sigma sigma add, map_sigma sigma t)

let encode proof =
  let rec encode_aux = function
  | Axiom i -> F((1, []), (2, []))
  | Par (n, p) -> U ((n, []),
                       map_psi (psi_1 n) (encode_aux p))
  | Tensor (p1, p2) -> let n = List.length (get_seq p1) in
                       B ((n, []),
                            map_psi (psi_2 n) (encode_aux p1),
                            map_psi (psi_3 n) (encode_aux p2))
  | Permutation (sigma, p) -> map_sigma sigma (encode_aux p) in
  (encode_aux proof, get_seq proof)


(*Decoding*)
(*Given a tree, extract the sorted indexes of its root addresses*)
let list_of_roots t =
  let rec aux = function
    | Unknown -> []

    | F ((n1, []), (n2, [])) -> [n1; n2]
    | F ((n1, []), _) -> [n1]
    | F (_, (n2, [])) -> [n2]
    | F (_, _) -> []

    | U ((n, []), t1) -> n::(aux t1)
    | U (_, t1) -> aux t1

    | B ((n, []), t1, t2) -> n::(aux t1)@(aux t2)
    | B (_, t1, t2) -> (aux t1)@(aux t2) in
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
  | Unknown -> failwith "Bad construction: incomplete tree"
  | F ((1, []), (2, [])) -> begin
    match s with
    | [A i; NA j] when i = j -> Permutation ([|2; 1|], Axiom i)
    | [NA i; A j] when i = j -> Axiom i
    | _ -> print_seq s; print_newline (); failwith "Bad construction: not an axiom"
    end
  | F (_, _) -> failwith "Bad construction: wrong addresses in axiom"
  | U ((n, w), t0) -> Par(n, decode (map_psi (psi_1_merged n) t0, aux_unpar s n))
  | B ((n, w), t1, t2) ->
      let sigma1 = Array.of_list (list_of_roots t1) in
      let m1 = Array.length sigma1 in
      let sigma2 = Array.of_list (list_of_roots t2) in

      let merged = sigma_merge sigma1 sigma2 n in

      let s1, s2 = seq_split s merged n m1 in
      let t1_map, t2_map = map_psi (alpha_1 merged m1 n) t1, map_psi (alpha_2 merged m1 n) t2 in
      let p1, p2 = decode (t1_map, s1), decode (t2_map, s2) in
      Permutation (get_perm sigma1 sigma2 n, Tensor (p1, p2))


(*Approximations*)
(*Given a tree, find the address of its first Unknown node, meaning the closest to the root, left to right*)
let rec unknown_list t =
  match t with
  | Unknown -> [[]]
  | F _ -> []
  | U(_, t') -> List.map (fun x -> Left::x) (unknown_list t')
  | B(_, t1, t2) -> List.map (fun x -> Left::x) (unknown_list t1) @ List.map (fun x -> Right::x) (unknown_list t2)

let find_first_unknown t =
  match unknown_list t with
  | [] -> None
  | a::l -> Some a

(*Given a sequent and an address, return the node_type of the subsequent addressed*)
let get_node_type_of_add s a =
  let n, w = a in
  let rec aux f w_curr = 
    match f, w_curr with
    | A _, [] -> Leaf
    | NA _, [] -> Leaf
    | P(_, _), [] -> Unary
    | T(_, _), [] -> Binary
    | P(f1, _), Left::xs -> aux f1 xs
    | P(_, f2), Right::xs -> aux f2 xs
    | T(f1, _), Left::xs -> aux f1 xs
    | T(_, f2), Right::xs -> aux f2 xs
    | _ -> failwith "Bad construction get_node_type_of_add" in
  aux (Array.of_list s).(n-1) w

let get_subformula_of_add s a =
  let n, w = a in
  let rec aux f w_curr = 
    match f, w_curr with
    | _, [] -> f
    | P(f1, _), Left::xs -> aux f1 xs
    | P(_, f2), Right::xs -> aux f2 xs
    | T(f1, _), Left::xs -> aux f1 xs
    | T(_, f2), Right::xs -> aux f2 xs
    | _ -> failwith "Bad construction get_subformula_of_add" in
  aux (Array.of_list s).(n-1) w

(*Replace an Unknown node in a tree*)
let rec replace_unknown_node t a node_type node_adresses =
  match t, a with
  | U(a', t'), Left::xs -> U(a', replace_unknown_node t' xs node_type node_adresses)
  | B(a', t1, t2), Left::xs -> B(a', replace_unknown_node t1 xs node_type node_adresses, t2)
  | B(a', t1, t2), Right::xs -> B(a', t1, replace_unknown_node t2 xs node_type node_adresses)
  | Unknown, [] ->
    begin
      match node_type, node_adresses with
      | Leaf, [a1; a2] -> let a1', a2' = add_sort a1 a2 in F(a1', a2')
      | Unary, [a1] -> U(a1, Unknown)
      | Binary, [a1] -> B(a1, Unknown, Unknown)
      | _ -> failwith "replace_unknown_node: wrong node arguments"
    end
  | _ -> failwith "replace_unknown_node: wrong tree arguments"
  
(*Given a mapping function from N to A, update it in case of a par*)
let mapping_update_par mapping n = 
  let m = Array.length mapping in
  let new_mapping = Array.make (m+1) (-1, []) in

  for i = 0 to n-2 do
    new_mapping.(i) <- mapping.(i)
  done;

  let (n', w') = mapping.(n-1) in
  new_mapping.(n-1) <- (n', Left::w');
  new_mapping.(n) <- (n', Right::w');

  for i = n+1 to m do
    new_mapping.(i) <- mapping.(i-1)
  done;

  new_mapping
  
(*Given a low approximation, update it in case of a tensor*)
let low_approx_update_par s' n =
  let m = Array.length s' in
  let low_approx_new = Array.make (m+1) false in

  for i = 0 to n-2 do
    low_approx_new.(i) <- s'.(i)
  done;

  low_approx_new.(n-1) <- true;
  low_approx_new.(n) <- true;

  for i = n+1 to m do
    low_approx_new.(i) <- s'.(i-1)
  done;

  low_approx_new

(*Given a sequent with a tensor, keep only a side of the tensor in the sequent*)
let rec aux_untensor_dir s n dir =
    match s, n with
    | T(g, d)::ys, 1 -> 
      begin
        match dir with
          | Left -> g::ys
          | Right -> d::ys
      end
    | x::xs, i when i > 1 -> x::(aux_untensor_dir xs (i-1) dir)
    | _ -> failwith "Bad construction aux_untensor_dir"

(*Given a set and indexes, remove the indexed elements in the set*)
let set_remove set indexes =
  let rec aux set_acc indexes_acc acc =
    match set_acc, indexes_acc, acc with
    | x::xs, i::is, j when i = j -> aux xs is (j+1)
    | x::xs, i::is, j when i > j -> x::(aux xs (i::is) (j+1))
    | x, [], i -> x
    | _ -> failwith "Bad construction set_remove" in

  aux set indexes 1

(*Given a mapping function from N to A, update it in case of a tensor*)
(* m is the number of formulas to be kept *)
let mapping_update_tensor mapping n m dir sigma = 
  let new_mapping = Array.make (m) (-1, []) in
  let acc = ref 0 in
  let (n_mapped, w_mapped) = mapping.(n-1) in
  for i = 0 to (Array.length mapping) - 1 do
    if sigma.(i) <> -1 then begin
      incr acc;
      match mapping.(i) with
      | (j, w) when j = n_mapped && w = w_mapped-> new_mapping.(!acc - 1) <- (j, w@[dir])
      | (j, w) -> new_mapping.(!acc - 1) <- (j, w)
    end
  done;

  if !acc <> m then failwith "Bad construction mapping_update_tensor2"
  else new_mapping

let approx (t, s) a =
  (*a: address of context in t, with the convention that Left is used in case of an unary node*)
  let rec approx_aux t s s' a mapping  =
  (*mapping: N -> A*)
  (*s is the high approximation: it contains all the formulas that can be applied at address a*)
  (*s' is the low approximation: it's a tab of booleans indicating if a formula in s is mandatory*)
    match t, a with
    | Unknown, [] -> mapping, s, s'
    | F(a1, a2), [] -> [|a1; a2|], 
                       [get_subformula_of_add s a1; get_subformula_of_add s a2],
                       [|true; true|]
    | U(_, _), [] -> 
      let children = list_of_roots t in
      List.iter (fun i -> s'.(i-1) <- true) children;

      mapping, s, s'
    
    | B(_, t1, t2), [] ->
      let children = list_of_roots t in
      List.iter (fun i -> s'.(i-1) <- true) children;

      mapping, s, s'

    | U((n,w), t), Left::xs -> 
      approx_aux (map_psi (psi_1_merged n) t)
                  (aux_unpar s n) 
                  (low_approx_update_par s' n)
                  xs
                  (mapping_update_par mapping n)
    | B((n,w), t_l, t_r), dir::xs -> 
      let t_c, t = match dir with
          | Left -> (t_l, t_r)
          | Right -> (t_r, t_l)
      in
      let m = List.length s in
      let indexes_t = list_of_roots t in
      let s_untensored = aux_untensor_dir s n dir in
      let s_new = set_remove s_untensored indexes_t in

      let context_empty = ((unknown_list t) = []) in

      let sigma = Array.make m (-1) in
      let m' = m - (List.length indexes_t) in
      let s'_new = Array.make m' false in

      let rec aux to_remove i acc =
        match to_remove with
        | x::xs when x = i -> aux xs (i+1) acc
        | x::xs when x > i -> 
          begin
            (if context_empty || (i = n) then s'_new.(acc-1) <- s'.(i-1)
            else ());
            sigma.(i-1) <- acc; aux (x::xs) (i+1) (acc+1)
          end
        | [] when i = m + 1 -> ()
        | [] -> 
          begin
            (if context_empty || (i = n) then s'_new.(acc-1) <- s'.(i-1)
            else ());
            sigma.(i-1) <- acc; aux [] (i+1) (acc+1)
          end
        | _ -> failwith "Bad construction approx2" in
      aux indexes_t 1 1;
      
      let reindex n = function
        | (i, dir::w) when i = n -> (sigma.(i-1), w)
        | (i, w) when i <> n -> (sigma.(i-1), w)
        | _ -> failwith "Bad construction approx3" in
    
      let t_c_new = map_psi (reindex n) t_c in
      approx_aux t_c_new s_new s'_new xs (mapping_update_tensor mapping n m' dir sigma)
    | _ -> failwith "Bad construction"

    in let mapping_base = Array.init (List.length s) (fun i -> (i + 1, [])) in
    approx_aux t s (Array.make (List.length s) true) a mapping_base 
    

(*Interactive proving*)
(*Check if a leaf application is correct*)
let check_leaf s s' n n' =
  let rec aux s_acc i a1 a2 =
    match s_acc with
    | [] -> a1, a2
    | x::xs when i <> n && i <> n' && (not s'.(i-1)) -> aux xs (i+1) a1 a2
    | x::xs when i = n -> aux xs (i+1) x a2
    | x::xs when i = n' -> aux xs (i+1) a1 x
    | _ -> raise MandatoryNotUsed in

  match aux s 1 (A(-1)) (A(-1)) with
  | A(i), NA(j) when i = j -> ()
  | NA(i), A(j) when i = j -> ()
  | _ -> raise NotDual

let print_rep_latex (t, s) print_function =
  let rec aux t_curr path depth =
    match t_curr with
    | Unknown -> Printf.printf "%s\\hypv{" (repeat_string space depth); 
                 let _, s_new, s'_new = approx (t, s) path in print_function s_new s'_new; print_string "}\n"
    | F(a1, a2) -> Printf.printf "%s\\axv{" (repeat_string space depth);
                   print_function [get_subformula_of_add s a1; get_subformula_of_add s a2] [|true; true|]; print_string "}\n"
    | U(a1, t1) -> aux t1 (path@[Left]) (depth + 1);
                   Printf.printf "%s\\parrv{" (repeat_string space depth);
                   let _, s_new, s'_new = approx (t, s) path in print_function s_new s'_new; print_string "}\n"
    | B(a1, t1, t2) -> aux t1 (path@[Left]) (depth + 1); print_newline ();
                       aux t2 (path@[Right]) (depth + 1);
                       Printf.printf "%s\\tensorv{" (repeat_string space depth);
                       let _, s_new, s'_new = approx (t, s) path in print_function s_new s'_new; print_string "}\n"
  in aux t [] 0

(*Check if a sequent is atomic*)
let rec is_atomic = function
  | [] -> true
  | (A _)::xs -> is_atomic xs
  | (NA _)::xs -> is_atomic xs
  | _ -> false

(*Given a representation and an address, try to auto complete the unknown node addressed by a*)
let atom_auto_complete t s a =
  let mapping, s', s'_low = approx (t, s) a in
  if is_atomic s' then 
    begin
      let rec mandatory_build s'_curr acc =
        match s'_curr with
        | [] -> []
        | x::xs when s'_low.(acc-1) = true -> (acc, x)::(mandatory_build xs (acc+1))
        | _::xs -> mandatory_build xs (acc+1) in
      match mandatory_build s' 1 with
        | [] -> if List.length s' = 2 then 
                  begin
                  (check_leaf s' s'_low 1 2);
                  (replace_unknown_node t a Leaf [mapping.(0); mapping.(1)]), true
                  end
                else t, false
        | [(n1, x)] -> begin
                      let rec complementary_build s'_curr acc =
                        match s'_curr, x with
                        | [], _ -> []
                        | (NA i)::xs, A j when i = j -> acc::(complementary_build xs (acc+1))
                        | (A i)::xs, NA j when i = j -> acc::(complementary_build xs (acc+1))
                        | _::xs, _ -> complementary_build xs (acc+1) in
                      match complementary_build s' 1 with
                        | [] -> raise ToName
                        | [n2] -> (check_leaf s' s'_low n1 n2);
                                  (replace_unknown_node t a Leaf [mapping.(n1-1); mapping.(n2-1)]), true
                        | _ -> t, false
                      end
        | [(n1, _); (n2, _)] -> (check_leaf s' s'_low n1 n2);
                                (replace_unknown_node t a Leaf [mapping.(n1-1); mapping.(n2-1)]), true
        | _ -> raise ToName

    end
  else t, false

(*Given a representation, iteratively autocomplete its holes, until a fixpoint is reached*)
let rec autocomplete t s =
  let list_unknown = unknown_list t in
  let t_new, modified = List.fold_left 
                        (fun (t', m') a -> 
                          let t'_new, m'_new = atom_auto_complete t' s a
                          in t'_new, (m'||m'_new))
                        (t, false) 
                        list_unknown 
  in 
  if modified then autocomplete t_new s
  else t_new


let prove_sequent s =
  let rec aux t_curr =
    let list_unknown = unknown_list t_curr in
    match list_unknown with 
    | [] -> print_string "Proven!\n\n"; print_proof_latex (decode (t_curr, s))
    | _ -> 
      begin
        print_rep_latex (t_curr, s) print_seq_low;
        print_newline ();
        let n_hole =
          if List.length list_unknown = 1 then 1
          else (print_string "Please choose the hole to work on:\n"; read_int ()) in
        let a' = (Array.of_list list_unknown).(n_hole - 1) in
        let mapping, s', s'_low = approx (t_curr, s) a' in
        print_seq_low s' s'_low;
        print_newline ();
        print_string "Please choose the rule to apply:\n";
        let n = read_int () in
        try begin
          match get_node_type_of_add s' (n, []) with
          | Unary -> print_newline (); aux (autocomplete (replace_unknown_node t_curr a' Unary [mapping.(n-1)]) s)
          | Binary -> print_newline (); aux (autocomplete (replace_unknown_node t_curr a' Binary [mapping.(n-1)]) s)
          | Leaf -> begin
            print_string "Please choose the dual atom to use:\n";
            let n' = read_int () in
            match get_node_type_of_add s' (n', []) with
            | Leaf -> print_newline (); check_leaf s' s'_low n n'; aux (replace_unknown_node t_curr a' Leaf [mapping.(n-1); mapping.(n'-1)])
            | _ -> failwith "prove_sequent: two atoms were expected"
            end
        end with
        | MandatoryNotUsed -> print_string "Error: you must use all highlighted formulas\n\n"; aux t_curr
        | NotDual -> print_string "Error: two dual atoms were expected\n\n"; aux t_curr
        | ToName -> print_string "Error: to name\n\n"; aux t_curr
        | Invalid_argument _ -> print_string "Error: index out of bounds\n\n"; aux t_curr
        | Failure error -> Printf.printf "Error: %s\n\n" error; aux t_curr
        | _ -> print_string "Error: please retry with a correct input\n\n"; aux t_curr
      end in
  aux Unknown
    

(*Proof examples*)
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

                                                                                
(*Examples from Click & Collect*)
let example1 = [P(NA 1, A 1)];;
let example2 = [P(NA 1, NA 2); T(A 2, A 1)];;
let example3 = [T(A 1, NA 2); T(A 2, NA 3); P(NA 1, A 3)];;
let example4 = [P(NA 1, T(A 1, NA 2)); A 2];;
let example5 = [P(P(NA 1, NA 2), NA 3); T(A 1, T(A 2, A 3))];;
let example6 = [P(NA 1, T(A 2, NA 3)); P(NA 2, T(A 1, A 3))];;
let example7 = [P(P(NA 1, NA 2), NA 3); T(A 1, T(A 2, A 3))];;
let example8 = [P(NA 1, P(NA 2, NA 3)); T(T(A 1, A 2), A 3)];;
let example9 = [P(T(A 1, NA 2), NA 3); P(NA 1, T(A 2, A 3))];;

let example10 = [A(5); A(4); T(NA(1), T(NA(2), T(NA(3), T(NA(4), NA(5))))); A(1); P(A(3), A(2))];;
                       
let _ = prove_sequent example4;;
