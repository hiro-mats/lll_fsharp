# lll_fsharp

LLL algorithm written by f#

格子暗号解読のための数学的基礎(ISBN-13: 978-4764905986)を参考として、
LLL基底簡約アルゴリズムを実装することを目標とした。

以下ではグラムシュミット分解 A=BC、Bは直交行列、Cは上三角行列に対し、
BをGSOベクトル行列、CをGSO係数行列と呼ぶ。

格子基底行列 A=(a(0),...,a(n)) (縦ベクトルを並べて行列を表記) が簡約パラメータdに対してLLL簡約されているとは、

1,AのGSO係数行列の要素の絶対値が全て1/2以下

2,AのGSOベクトル行列 B=(b(0),...,b(n)) (縦ベクトルを並べて行列を表記) に対し、 d*||b(k-1)||^2 <= ||p(k)(a(k))||^2  (ただしp(k)はa(1),...,a(k-1)の張る空間に対する直交補空間への直交射影)

の2条件を満たすことである。

LLL簡約とは格子基底行列Aから同じ格子を張るLLL簡約されている格子基底行列A'を得る操作である。
特にこのアルゴリズムにおいては関数 gsoupdate を用いることで、
元の格子基底行列の隣り合う列を入れ替える操作に対するGSO情報の更新を効率的に行っている。

今回の目標として、関数 lll_reduce を実装した。
これにに格子基底行列と簡約パラメータを代入することで、
LLL簡約済基底行列とそのグラムシュミット直交係数行列が出力される。
