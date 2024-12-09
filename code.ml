#require "zarith";;


(*-------------------------------------  1 Rationnel de Gauss------------------------------------------------- *)



               (*----------------------- 1.1 Module Zarith--------------------------------------*)

let exp1 = Q.of_string "123456789987654321/5678900987654";;

(* x1/y1 *)

let exp2 = Q.of_string "-67831300097/236543209890003";;

(*  x2 /y2 *)


(*le denominateur  y1 * y2  *)
let den_exp1_exp2 =Z.mul (Q.den exp1) (Q.den exp2);;


(* le numerateur  x1*y2 + x2*y1 *)
let num_exp1_exp2 =Z.add (Z.mul(Q.num exp1)(Q.den exp2))(Z.mul(Q.num exp2)(Q.den exp1));;


(* exp1 + exp2  *)
let mult_exp1_exp2 = Q.make num_exp1_exp2 den_exp1_exp2 ;;

(*Q.to_string  mult_exp1_exp2 ;;*)


               (*-------------------1.2 Algèbre effective des rationnels de Gauss--------------*)

type rationnel = Q.t                

type r_gauss = Indefini |  Rationnel of rationnel*rationnel

                         (*Les fonctions sur les rationnels de Gauss *)


exception Parametre_undef;;

(* Partie réelle *)

let partie_reelle rg  = match rg with
   | Rationnel (re,_) -> re
   | Indefini -> raise Parametre_undef
;;


(* Partie imaginaire *)

let partie_imaginaire rg = match rg with
   | Rationnel (_,img) -> img
   | Indefini ->  raise Parametre_undef
;;


(* test si c'est egale a 0)*)

let is_zero_gauss rg = match rg with
  |Indefini ->  raise Parametre_undef
  | Rationnel(re,img) ->  (Q.equal Q.zero re ) && (Q.equal Q.zero img) ;;


 (* test l'egalite*)

let equal_gauss rg1 rg2  = match rg1,rg2 with
  |Indefini,_ | _,Indefini-> false
  |Rationnel(re1,img1), Rationnel(re2,img2) -> (Q.equal re1 re2) && (Q.equal img1 img2);;

(* addition *)

let add_gauss rg1 rg2 = match rg1,rg2 with
  | Rationnel(re1,img1),Rationnel(re2,img2) -> Rationnel ((Q.add re1 re2),(Q.add img1 img2))
  | _ -> Indefini
;;

(* multiplication *)

let mult_gauss rg1 rg2 = match rg1,rg2 with
  | Rationnel(re1,img1),Rationnel(re2,img2) ->
    let re = Q.sub(Q.mul re1 re2)(Q.mul img1 img2) in
    let img =Q.add (Q.mul re1 img2) (Q.mul re2 img1) in
    Rationnel(re,img)
  |_,_ -> Indefini
;;

(*oppose*)

 let oppose_gauss rg = match rg with
  |Rationnel(re,img) -> Rationnel(Q.neg re, Q.neg img)
  |Indefini -> Indefini;;

(*fonction auxiliare qui calcule le conjuguer d'un r_gauss*)

 let conjuguer_gauss rg = match rg with
  |Indefini -> Indefini
  |Rationnel(re,img) -> Rationnel(re,Q.neg img)
;;

(* inverse *)

let inverse_gauss rg = match rg with
  |Indefini -> Indefini
  |Rationnel(re,img) ->  let denom = Q.add (Q.mul re re) (Q.mul img img) in
    Rationnel (Q.div re denom, Q.neg (Q.div img denom));;



 (*---------------------------------2 Polynômes à coefficients dans Q(i)----------------------------------*)




                      (*-----------------2.1 Algèbre effective Q(i)[X] *---------------------*)


(* les polynomes doivent etre ecrit comme dans le tp du moment que aucune spesification sur n'a etait donne
   exemple :
   let poly1 = [(0,Rationnel (Q.of_int 1, Q.zero)); (1, Rationnel(Q.of_int 2, Q.zero))]
    Polynôme 1 + 2X 
*)

type poly = (int * r_gauss) list
    



(* fonction purge : (int*r_gauss) list -> poly
L'appel purge l renvoie la liste l à laquelle on a enlevé les coefficients
égaux à 0. *)


let rec purge (l: (int * r_gauss) list): poly= match l with
  [] -> []
  |h::t -> if (is_zero_gauss (snd h) ) then purge (t)
    else h::(purge t);;

(* fonction coeff : poly -> int -> r_gauss
L'appel coeff p i renvoie le coefficient de X^i dans le développement
du polynôme p *)

let rec coeff (pol:poly) (n:int):r_gauss = match pol with
    [] -> Rationnel(Q.zero,Q.zero) 
    |h::t -> if(fst h = n) then snd h
             else coeff t n
;;

(* fonction degre : poly-> int
L'appel degre p renvoie le degré du polynome p
le degré du polynome nul sera noté -1 *)

let rec degre (p:poly):int = match p with
    [] -> -1
    |h::[] -> fst h
    |h::t ->degre t
;;

(* fonction cd: poly->r_gauss
L'appel cd p renvoie le coefficient dominant du polynôme p
*)

let cd (p:poly) : r_gauss = coeff p (degre p);;

(* fonction multCoeff : poly -> r_gauss -> poly
L'appel multCoeff p co renvoie le polynôome p multiplié par le rationnel co *)

let multCoeff(p:poly) (co:r_gauss) : poly =
  purge (List.map (fun (deg, coeff) ->
    let new_coeff = mult_gauss coeff co in
    (deg, new_coeff)) p)

(* fonction add : poly -> poly -> poly
L'appel add p q renvoie la somme des polynômes p et q *)

let rec add (p:poly) (q:poly) : poly = match p, q with
  | [], [] -> []
  | [], q -> q
  | p, [] -> p
  | (deg1, coeff1) :: t1, (deg2, coeff2) :: t2 ->
      if deg1 = deg2 then
        let added_coeff = add_gauss coeff1 coeff2 in
        purge ((deg1, added_coeff) :: add t1 t2)
      else if deg1 < deg2 then
        purge ((deg1, coeff1) :: add t1 (q))
      else
        purge ((deg2, coeff2) :: add p (t2))



 (*fonction sub : poly -> poly -> poly
L'appel sub p q renvoie la difference du polynôme p  avec le polynôme q *)

let sub (p1:poly) (p2:poly) =
  let p2' = List.map (function rg -> ((fst rg) ,oppose_gauss(snd rg))) p2 in
  add p1 p2';;


let concat = String.concat;;


(* Fonction pour convertir un rationnel de Gauss en chaîne de caractères *)

let string_of_r_gauss rg = match rg with
  | Indefini -> "Indefini"
  | Rationnel(re, img) ->
    "(" ^ Q.to_string re ^ " + i" ^ Q.to_string img ^ ")"

(* Fonction récursive pour convertir un polynôme en chaîne de caractères *)
    
let rec string_of_poly p = match p with
  | [] -> ""
  | (deg, coeff)::t ->
    let coeff_str = string_of_r_gauss coeff in
    let term = if deg = 0 then coeff_str
               else coeff_str ^ "X^" ^ string_of_int deg in
    let next = string_of_poly t in
    if next = "" then term else term ^ " + " ^ next;;



(* multXn : poly -> int -> poly
L'appel multXn p m renvoie le polynome X^m*p*)

let rec multXn (p:poly) (m:int) : poly = match p with
  []->[]
  |p when m=0-> p (* m=0 donc le monome est egale a X⁰ = 1 donc une mult par 1 *)
  |(deg,rg)::t ->(deg + m,rg  )::(multXn t m);;

(* mult_naive : poly -> poly -> poly
mult_naive p q renvoie la multiplication des polynômes p et q en utilisant
la méthode naïve *)

let rec mult_naive (p1:poly) (p2:poly) : poly =
  match p1, p2 with
  | [], _ | _, [] -> []
  | (deg1, coeff1) :: t1, _ ->
    add (multCoeff (multXn p2 deg1) coeff1) (mult_naive t1 p2);;


(*choisir_coupure : int -> int -> int
choisir_coupure d1 d2 renvoie la moitié du plus petit entier pair supérieur à
d1 et d2. Cette fonction est utilisée dans l'algorithme de Karatsuba.
*)

let choisir_coupure (d1:int) (d2:int) : int =
  let n = max d1 d2 in
  if n mod 2 == 0 then n / 2
  else (n + 1) / 2
;;


(* cut : poly -> int -> poly * poly
   La fonction cut p i renvoie la paire de polynômes (p0, p1)
   tels que p = p0 + X^i * p1 avec deg p0 < i.
   Utilisée dans l'algorithme de Karatsuba. *)

let rec cut (p:poly) (i:int) : poly * poly =
  match p with
  | [] -> [], []
  | (d, c) :: t when d < i -> let p1, p2 = cut t i in
                              (d, c) :: p1, p2
  | (d, c) :: t -> let p1, p2 = cut t i in
                   p1, (d - i, c) :: p2
;;


(* karatsuba: poly -> poly -> int -> poly
kartsuba p q k renvoie le produit p*q en utilisant la méthode de Karatsuba
si l'un des polynômes a son degré <k alors on utilise la méthode naive
*)

let rec karatsuba (p:poly) (q:poly) k =
    if (degre p <= k || degre q <= k) then
      mult_naive p q
    else
      let k = choisir_coupure (degre p) (degre q) in
      let (a0,a1) = cut p k in
      let (b0,b1) = cut q k in
      let p0 = karatsuba a0 b0 k in
      let p2 = karatsuba a1 b1 k in
      let u = (karatsuba (add a0 a1)(add b0 b1) k) in
      let p1 = sub (sub u p0) p2 in
      add (add(multXn p1 (k/2)) (multXn p2 (k))) p0
;;


(* renverse int -> poly -> poly:
   renverse k p renvoie le polynome Rev_k(p) (cf algorithme de Newton) *)

exception Ordre_bas;;

let renverse (k:int) (p:poly) : poly =
  if k < degre p then
    raise Ordre_bas
  else
    List.rev (List.map (fun (deg, coeff) -> (k - deg, coeff)) p);;


(*moduloXn : poly -> int -> poly
  moduloXn p n renvoie le reste de la division de p par X^n *)

let moduloXn (p:poly) (i:int) : poly =
  List.filter (fun (deg, _) -> deg < i) p;;



let p_derive_0 = (0,Rationnel(Q.zero,Q.zero));; 
let p_derive_1 = [0,Rationnel(Q.one,Q.zero)];;


(* Calcul de l'inverse d'un polynôme b modulo X^n en utilisant l'algorithme de Newton *)
         
let inverse_mod (p: poly) (m: int) : poly =
  if p = [p_derive_0] then failwith " division par 0"
  else
  let (deg, co) = List.hd p in
  if co <> (Rationnel (Q.one, Q.zero)) then failwith "impossible, le terme constant doit être être égal à un"
  else
  let rec aux g i =
  let j = 2. ** i in
  if (int_of_float j) >= m then g
  else let i = i +. 1. in let gp = karatsuba g (sub [(0, Rationnel (Q.one, Q.zero))] (karatsuba p g 1)) 1
  in let g = add g (moduloXn gp (int_of_float (j *. 2.)))
  in (aux g i)
  in moduloXn (aux [(0, Rationnel (Q.one, Q.zero))] 0.) m;;


(* div : poly -> poly -> poly
div p1 p2 renvoie un couple de polynome (q,r)
tel que q est le quotient et r le reste de la division de p1 par p2
en utilisant l'inversion de Newton *)

let div (a: poly) (b: poly) : poly * poly =
  let n = degre a in
  let m = degre b in
  if b = [] then failwith " div par 0"
  else if n < m then ([], a)
  else
    let b_m = cd b in
    let inv_b_m = inverse_gauss b_m in
    let b_rev = renverse m b in
    let b_rev_bm = multCoeff b_rev inv_b_m in
    let inv_b = inverse_mod b_rev_bm (n - m + 1) in
    let a_rev = renverse n a in
    let q_rev = mult_naive a_rev inv_b in
    let q_rev_mod = renverse (n - m) (moduloXn q_rev (n - m + 1)) in
    let q = multCoeff q_rev_mod inv_b_m in
    let r = sub a (mult_naive b q) in
    (purge q, purge r)


                                                      (*-------------2.2 Algorithme d’Euclide étendu-------------*)


(* Calcul Bezout *)
let rec calcul_bezout (e: poly) (alpha0: poly) (beta0: poly) (f: poly) (alpha1: poly) (beta1: poly) (q: poly) : poly * poly * poly =
  let _,r = div e f in
  if r = [] then (f, alpha1, beta1)
  else
    let alpha = sub alpha0 (mult_naive alpha1 q) in
    let beta = sub beta0 (mult_naive beta1 q) in
    let q_next, _ = div f r in
    calcul_bezout f alpha1 beta1 r alpha beta q_next
;;

(* Calcul euclide etendu (P, alpha, beta) *)
let pgcd_etendu (e: poly) (f: poly) : poly * poly * poly =
  if f = [] then (f, [(0, Rationnel (Q.one, Q.zero))], [(0, Rationnel (Q.zero, Q.zero))])
  else 
    let q, _ = div e f in
    let prg0 = [(0, Rationnel (Q.zero, Q.zero))] in
    let prg1 = [(0, Rationnel (Q.one, Q.zero))] in
    calcul_bezout e prg1 prg0 f prg0 prg1 q
;;


               (*------------2.3 Division suivant les puissances croissantes-------------------*)


let div_croissante (a:poly) (b:poly) : poly*poly = failwith " a faire";;
  


                        (*------------2.4 Dérivation des polynômes---------*)

let p_derive_0 = (0,Rationnel(Q.zero,Q.zero));;
let p_derive_1 = [0,Rationnel(Q.one,Q.zero)];;

(* multiplication d'un polynome p par un terme d'un polynome (un monome mais pas en liste)  *)
  
let mult_term_poly (d1, c1) p =
  List.map (fun (d2, c2) ->
    let c = match (c1, c2) with
      | (Rationnel(r1, i1), Rationnel(r2, i2)) -> Rationnel(Q.mul r1 r2, Q.mul i1 i2)
      | _ -> Indefini
    in
    (d1 + d2, c)
  ) p;;


(* prend un poly avec un seul terme et le derive selon le methode de leibniz *)

let derive_poly p =
  let rec derive_term (deg, coeff) =
    if deg = 0 then  p_derive_0 else
    match coeff with
    | Indefini -> (deg - 1, Indefini)
    | Rationnel (re, img) ->
      let new_re = Q.mul (Q.of_int deg) re in
      let new_img = Q.mul (Q.of_int deg) img in
      (deg - 1, Rationnel(new_re, new_img))
  in
  let rec aux acc = function
    | [] -> List.rev (purge acc)
    | (deg , coeff) :: t ->
      let a = (0,coeff) in
      let b = (deg,Rationnel(Q.one,Q.zero)) in
      let p0 = derive_term a in
      let p1 = derive_term b in 
      let a0 = mult_term_poly a [p1] in
      let b0 =  mult_term_poly b [p0] in
      add a0 b0  
  in
  aux [] p;;

(* Prend un polynome p et le derive selon "diviser pour reigner" et Leibniz *)

let rec derive_leibniz (p:poly) =
  let rec split_list lst =
    let rec aux acc i lst = match lst with
      | [] -> (List.rev acc, [])
      | h::t -> if i <= 0 then (List.rev acc, lst) else aux (h::acc) (i-1) t
    in
    aux [] (List.length lst / 2) lst
  in
  let (p1, p2) = split_list p in
  let acc1 = [] and  acc2 = [] in
  let a1 = (match p1 with
  | [] -> []
  | x::[] as p0 ->(derive_poly p0)@ acc1 
  | l  -> (derive_leibniz l)@ acc1 ) in
  let a2 = (match p2 with
  | [] -> []
  | x::[] as p0 ->(derive_poly p0)@ acc2 
  | l  -> (derive_leibniz l)@ acc2)
  in
  add a1 a2;;


(* Définition des polynômes pour les tests *) 

let (null_poly:poly) = [];;

let poly0 = [(0,Rationnel (Q.of_int 1, Q.zero))];;  (* Polynôme constant 1 *)

let poly1 = [(0,Rationnel (Q.of_int 1, Q.zero)); (1, Rationnel(Q.of_int 2, Q.zero))];;  (* Polynôme 1 + 2X *)

let poly2 = [(0, Rationnel(Q.of_int 3, Q.zero))] ;;  (* Polynôme constant 3 *)

let poly3 = [(1,Rationnel(Q.of_int 1, Q.zero))]  (* Polynôme X (pas de terme constant) *)

let poly4 = [(0, Rationnel(Q.of_int 1, Q.zero)); (2, Rationnel(Q.of_int 4, Q.zero)); (3,Rationnel (Q.of_int 2, Q.zero))];;  (* Polynôme 1 + 4X^2 + 2X^3 *)

let poly5 = [(0,Rationnel (Q.of_int 2, Q.zero)); (1, Rationnel(Q.of_int 3, Q.zero)); (2, Rationnel(Q.of_int 4, Q.zero))] ;; (* Polynôme 2 + 3X + 4X^2 *)

let poly6 = [(0,Rationnel (Q.of_int 1, Q.zero)); (3, Rationnel(Q.of_int 2, Q.zero))];;  (* Polynôme 1 + 2X^3 *)

let poly7 = [(0, Rationnel(Q.of_int 1, Q.zero)); (1,Rationnel (Q.of_int (-1), Q.zero))];;
(* Polynôme 1 - X *)
let poly8 = [(0,Rationnel (Q.of_int 1, Q.zero)); (1, Rationnel(Q.of_int 1, Q.zero)); (2,Rationnel (Q.of_int 1, Q.zero))] ;; (* Polynôme 1 + X + X^2 *)

let poly9 = [(0, Rationnel(Q.of_int 1, Q.zero)); (1, Rationnel(Q.of_int 2, Q.zero)); (2, Rationnel(Q.of_int 3, Q.zero)); (3, Rationnel(Q.of_int 4, Q.zero))];;  (* Polynôme 1 + 2X + 3X^2 + 4X^3 *)


