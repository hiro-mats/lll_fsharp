module Latticecript

(*
整数ベクトルたちの生成する格子を考える。特にベクトルたちは一次独立とする。
これらのベクトルを縦ベクトルとして並べた行列を格子基底行列という。
特に格子基底行列が正方行列となるときを考える。
このときに生成される格子を保ったまま各ベクトルを短くする操作のことを簡約という。
今回はその中でもLLL簡約と呼ばれているアルゴリズムを実装することを目標とする。
*)

open MathNet.Numerics.LinearAlgebra

// リストの頭から項数がk個のリストを取る(0番目からk-1番目までを返す) 
let head_k_list (list:'a list) k =list.[..(k-1)]

// listのi番目からk-1番目までのk-i項からなるリストを返す 
let itok_list (list:'a list) i k =list.[i..(k-1)]

// リストのk-1番目とk番目の対を返す 
let rec k_1andkth list k=
 if k=1 then (List.head list,List.head(List.tail list))
 else k_1andkth (List.tail list) (k-1)

//リストからリストへの関数、例：[1,2,3,4,5]に対し[15;14;12;9;5]を返す 
let rec sumtail (list:double list) =
 match list with
  | [] -> []
  | [_] -> [List.head list]
  | fst::rest -> (fst+(List.head(sumtail rest)))::(sumtail rest)

//ベクトルの絶対値の二乗を返す
let abs2 (v:Vector<double>) = v.DotProduct(v)

// ベクトルの(空でない)リストに対しそれらを足し合わせたベクトルを返す
let rec sumvec (list:Vector<double> list) =
   match list with
   | [_] -> List.head list
   | head :: tail -> List.head list + sumvec (List.tail list)

//格子基底行列aに対し、第一因子:直交行列　第二因子:GSO係数行列を返す 
let gso (a:Matrix<double>) =
 let n = a.ColumnCount in
  let ai i = a.Column(i) in
  let rec m i j = if i>j then 0. elif i = j then 1. else ((ai j).DotProduct((bi i)))/ ((bi i).DotProduct((bi i)))
      and bi i = if i = 0 then ai 0 else ((ai i) - sumvec [for j in 0 .. i-1 -> (m j i)*(bi j)]) in
  let b0 = [for i in 0 .. n-1 -> (bi i)] in
 (DenseMatrix.ofColumnSeq b0 , DenseMatrix.init n n (fun i j -> (m i j)))

//二つのベクトルの組を第0要素が小さくなるように取り直す
let sort2 (u, v) = if (abs2 u)<(abs2 v) then (u,v)
                                     else (v,u)

//Lagrange基底簡約により二次元格子の逐次最小基底を取る
let rec lagrange ((v1:Vector<double>), (v2:Vector<double>)) = 
 let q = -(round ((v1.DotProduct(v2))/(abs2 v1))) in
 let v3 = v2 + q * v1 in
    if abs2 v3 >= abs2 v1 then (v1,v3) 
    else lagrange (v3, v1) 


//格子基底行列aとそのGSO係数行列cに対し、
//aのなす格子を保ったままGSO基底行列の(i,j)番目の絶対値が1/2以下となる格子基底行列a'と
//そのGSO係数行列c'を返す
let subsizereduce (a:Matrix<double>) (c:Matrix<double>) i j =
 let n = a.ColumnCount in
 let m = c.[i,j] in
 if m ** 2. > 0.25 then 
  let ai i = a.Column(i) in
  let ci i = c.Column(i) in
  let q = round m in
  let a0 = [for k in 0 .. (n-1) -> if k=j then (ai j)-q*(ai i) else ai k] in
  let c0 = [for k in 0 .. (n-1) -> if k=j then (ci j)-q*(ci i) else ci k] in
  (DenseMatrix.ofColumnSeq a0,DenseMatrix.ofColumnSeq c0)
 else (a,c)

//格子基底行列aとそのgso係数行列cに対し
//aのなす格子を保ったままGSO基底行列の各要素の絶対値が1/2以下となる格子基底行列a'と
//そのGSO係数行列c'を返す
let sizereduce (a:Matrix<double>) =
 let n = a.ColumnCount
 let c = snd(gso a)
 let rec hojo (a0,c0) i j =
  if j=n-1 && i=0 then (subsizereduce a0 c0 i j)
  elif i=0 then hojo (subsizereduce a0 c0 i j) j (j+1)
  else hojo (subsizereduce a0 c0 i j) (i-1) j
 in
 hojo (a,c) 0 1

//行列を縦ベクトルで(b0,b1,...,bn)としたときにそれらの絶対値の二乗からなるリスト(二乗リスト)を返す
let squarenormvector (a:Matrix<double>) =
 let rec hojo (a:Matrix<double>) =
  if a.ColumnCount = 1 then [abs2(a.Column(0))]
  else abs2(a.Column(0))::(hojo (a.RemoveColumn(0)))
 in
 hojo a

//格子行列のgso係数行列cとgsoベクトルの二乗リストblistと整数kに対し
//格子行列のk-1列目とk列目を入れ替えたときのgso係数行列とgsoベクトルの二乗リストを返す
let gsoupdate (c:Matrix<double>) blist k =
 let n = c.ColumnCount in
 let ck_1k = c.[k-1,k] in
 let bk_1=fst(k_1andkth blist k) in
 let bk = snd(k_1andkth blist k) in
 let ck_1=(ck_1k**2.)*bk_1+bk in
 let ck = bk_1*bk/ck_1 in
 let rec updateb b i =
  if i=n then []
  elif i=k-1 then
   ck_1::ck::List.tail (List.tail b)
  else (List.head b)::(updateb (List.tail b) (i+1))
 in
 let newb = updateb blist 0 in
 let nu i j = 
  if i=j then 1.
  elif i>j then 0.
  elif i=k-1&&j=k then c.[k-1,k]*bk_1/ck_1
  elif j=k-1 then c.[i,k]
  elif j=k then c.[i,k-1]
  elif i=k-1 then (c.[k,j]*bk+c.[k-1,k]*c.[k-1,j]*bk_1)/ck_1
  elif i=k then c.[k-1,j]-c.[k-1,k]*c.[k,j]
  else c.[i,j]
 in
 let newc = DenseMatrix.init n n (fun i j -> nu i j) in
 (newb,newc)


//格子基底行列aと簡約パラメータd(1未満、1に近いほど高精度)に対して
//aをLLL簡約した格子基底行列a'とa'のGSO係数行列c'を返す
let lll_reduce (a:Matrix<double>) d =
 let n = a.ColumnCount in
 let b = fst(gso a) in
 let c = snd(gso a) in
 let kth_reduce a c k =
  let rec kth_hojo (a,c) j k =
   if j=0 then subsizereduce a c j k
   else kth_hojo (subsizereduce a c j k) (j-1) k
  in
  kth_hojo (a,c) (k-1) k
 in
 let rec lll_hojo (a,c) blist k =
  let c0= snd(kth_reduce a c k) in
  let mu2 = c0.[k-1,k]**2.0 in
  let bk_1=fst(k_1andkth blist k) in
  let bk = snd(k_1andkth blist k) in
   if bk >= (d-mu2)*bk_1 then 
    if k=n-1 then (a,c)
    else lll_hojo(kth_reduce a c (k+1)) blist (k+1)
   else 
    let updated = gsoupdate c blist k in
    lll_hojo (kth_reduce (DenseMatrix.ofColumnSeq[for i in 0 .. (n-1) -> if i=(k-1) then a.Column(k) elif i=k then a.Column(k-1) else a.Column(i)]) (snd(updated)) (max 1 (k-1))) (fst(updated))  (max 1 (k-1))
 in
 lll_hojo (a,c) (squarenormvector b) 1


let a1 = matrix [[-2.;3.;2.;8.]
                 [7.;-2.;-8.;-9.]
                 [7.;6.;-9.;6.]
                 [-5.;-1.;-7.;-4.]]


[<EntryPoint>]
// test
let main args =
    printfn "%A" (lll_reduce a1 0.99)
    0