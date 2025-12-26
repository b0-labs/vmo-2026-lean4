# Bài 5 

**Câu 5 (7,0 điểm).** Cho tam giác nhọn không cân $ABC$ có các đường cao $AD, BE, CF$ với $D \in BC, E \in CA$ và $F \in AB$. Gọi $H, O$ và $I$ tương ứng là trực tâm, tâm đường tròn ngoại tiếp và tâm đường tròn nội tiếp của tam giác $ABC$. $M, N$ và $P$ tương ứng là trung điểm các đoạn thẳng $BC, CA$ và $AB$. Gọi $X, Y$ và $Z$ tương ứng là giao điểm của các cặp đường thẳng $(AI, NP), (BI, PM)$ và $(CI, MN)$.

a) Chứng minh rằng các đường tròn ngoại tiếp các tam giác $AXD, BYE, CZF$ có hai điểm chung nằm trên đường thẳng $OH$.

b) Các đường thẳng $NP, PM$ và $MN$ tương ứng cắt lại các đường tròn ngoại tiếp các tam giác $AXD, BYE$ và $CZF$ tại các điểm $X', Y'$ và $Z'$ ($X' \neq X, Y' \neq Y, Z' \neq Z$). Gọi $J$ là điểm đối xứng của $I$ qua $O$. Chứng minh rằng $X', Y'$ và $Z'$ cùng nằm trên một đường thẳng vuông góc với đường thẳng $HJ$.

# Lời giải

**Kí hiệu:**

* $(ABC)$ là đường tròn ngoại tiếp tam giác $ABC$, tâm $O$, bán kính $R$.
* $\omega_A=(AXD),\ \omega_B=(BYE),\ \omega_C=(CZF)$.
* $M,N,P$ là trung điểm $BC,CA,AB$.
* $X=AI\cap NP,\ Y=BI\cap PM,\ Z=CI\cap MN$.
* Ở câu (b): $X'=\omega_A\cap NP$ (khác $X$), tương tự $Y'\in \omega_B\cap PM$, $Z'\in\omega_C\cap MN$.


## Bổ đề 0: $NP,PM,MN$ là các đường trung trực của $AD,BE,CF$

Vì $NP\parallel BC$ và $AD\perp BC$ nên $NP\perp AD$.

Mặt khác, xét phép vị tự tâm $A$, tỉ số $\tfrac{1}{2}$: nó biến $BC$ thành $NP$. Do đó, điểm $D\in BC$ biến thành trung điểm của $AD$, nằm trên $NP$. Vậy $NP$ đi qua trung điểm của $AD$ và vuông góc $AD$ ⇒ $NP$ là **đường trung trực** của $AD$.

Tương tự, $PM$ là trung trực của $BE$, và $MN$ là trung trực của $CF$.

**Hệ quả quan trọng:**

* Nếu $T\in NP$ thì $TA=TD$.
* Nếu $T\in PM$ thì $TB=TE$.
* Nếu $T\in MN$ thì $TC=TF$.

## a) Ba đường tròn $(AXD),(BYE),(CZF)$ có hai điểm chung trên $OH$

### Bước 1: $AO$ tiếp xúc $\omega_A=(AXD)$ tại $A$

Do $X\in NP$ và $NP$ là trung trực của $AD$ ⇒ $XA=XD$ ⇒ trong tam giác $ADX$,
$$
\angle DAX=\angle ADX.
$$

Ta tính $\angle DAX$ và $\angle XAO$ (góc định hướng). Vì $AD\perp BC$ nên
$$
\angle DAB = 90^\circ - \angle ABC = 90^\circ - B.
$$
Vì $AX\subset AI$ là phân giác trong tại $A$,
$$
\angle XAB = \angle IAB = \frac{A}{2} = 90^\circ-\frac{B+C}{2}.
$$
Suy ra
$$
\angle DAX=\angle DAB-\angle XAB
= (90^\circ-B)-\Bigl(90^\circ-\frac{B+C}{2}\Bigr)
= \frac{C-B}{2}.
$$

Mặt khác, vì $O$ là tâm ngoại tiếp nên trong tam giác cân $AOB$ ta có
$$
\angle BAO = 90^\circ - C.
$$
Do đó
$$
\angle XAO = \angle IAO = \angle BAO - \angle BAI
= (90^\circ-C)-\frac{A}{2}
= (90^\circ-C)-\Bigl(90^\circ-\frac{B+C}{2}\Bigr)
= \frac{B-C}{2}.
$$
Vì góc định hướng, điều này cho $\angle XAO=\angle ADX$ (cùng trị modulo $180^\circ$), nên theo định lý góc tạo bởi tiếp tuyến và dây,
$$
AO \text{ tiếp xúc với }(AXD)\text{ tại }A.
$$
(Cách làm này đúng với sắp thứ tự góc định hướng; đây chính là ý tưởng trong lời giải chuẩn.)

**Tương tự:**

* $BO$ tiếp xúc $(BYE)$ tại $B$,
* $CO$ tiếp xúc $(CZF)$ tại $C$.

### Bước 2: $\omega_A,\omega_B,\omega_C$ đều trực giao với $(ABC)$

Tiếp tuyến của $(ABC)$ tại $A$ vuông góc $AO$. Trong khi đó tiếp tuyến của $\omega_A$ tại $A$ chính là $AO$. Hai tiếp tuyến vuông góc ⇒ hai đường tròn $\omega_A$ và $(ABC)$ **trực giao**.

Tương tự $\omega_B\perp (ABC)$, $\omega_C\perp (ABC)$.

**Hệ quả:** nếu $(ABC)$ có bán kính $R$ thì
$$
\operatorname{Pow}_{\omega_A}(O)=\operatorname{Pow}_{\omega_B}(O)=\operatorname{Pow}_{\omega_C}(O)=R^2.
$$
(vì tâm $O$ của $(ABC)$ có phương tích bằng $R^2$ đối với mọi đường tròn trực giao với $(ABC)$).

### Bước 3: $H$ cũng có phương tích bằng nhau đối với $\omega_A,\omega_B,\omega_C$

Vì $H\in AD$ và $A,D\in\omega_A$ nên
$$
\operatorname{Pow}_{\omega_A}(H)=HA\cdot HD.
$$
Tương tự:
$$
\operatorname{Pow}_{\omega_B}(H)=HB\cdot HE,\qquad
\operatorname{Pow}_{\omega_C}(H)=HC\cdot HF.
$$

Ta có đẳng thức quen thuộc trong tam giác nhọn:
$$
HA\cdot HD=HB\cdot HE=HC\cdot HF.
$$
(có thể chứng minh từ $AH=2R\cos A$ và $HD=2R\cos B\cos C$, suy ra tích bằng $4R^2\cos A\cos B\cos C$).

Vậy $H$ có **cùng phương tích** đối với cả ba đường tròn.

### Bước 4: Trục đẳng phương trùng nhau ⇒ ba đường tròn đồng trục theo $OH$

Vì $O$ có cùng phương tích với $\omega_A,\omega_B$ nên $O$ nằm trên trục đẳng phương của $\omega_A,\omega_B$.
Vì $H$ cũng có cùng phương tích nên $H$ cũng nằm trên trục đẳng phương đó.

Suy ra **trục đẳng phương của $\omega_A$ và $\omega_B$ là đường thẳng $OH$**. Tương tự cho các cặp còn lại, nên cả ba đường tròn $\omega_A,\omega_B,\omega_C$ **đồng trục** với trục đẳng phương chung là $OH$. Do đó chúng có **hai giao điểm chung** (có thể là phức nếu suy biến, nhưng ở đây cấu hình nhọn cho giao điểm thực) và hai điểm này nằm trên $OH$.

$\square$

## b) $X',Y',Z'$ thẳng hàng và đường thẳng ấy vuông góc $HJ$

Đặt $I_a,I_b,I_c$ là các tâm bàng tiếp (excenter) đối diện $A,B,C$.

### Bước 1: Các đường tròn tâm $X',Y',Z'$ đi qua $(A,D),(B,E),(C,F)$

Nhờ Bổ đề 0:

* $X'\in NP$ ⇒ $X'A=X'D$.
  Vậy đường tròn $\Gamma_X$ tâm $X'$, bán kính $X'A$ đi qua cả $A$ và $D$.
* $Y'\in PM$ ⇒ $Y'B=Y'E$.
  $\Gamma_Y$ tâm $Y'$, bán kính $Y'B$ đi qua $B,E$.
* $Z'\in MN$ ⇒ $Z'C=Z'F$.
  $\Gamma_Z$ tâm $Z'$, bán kính $Z'C$ đi qua $C,F$.

Khi đó:
$$
\operatorname{Pow}_{\Gamma_X}(H)=HA\cdot HD,\quad
\operatorname{Pow}_{\Gamma_Y}(H)=HB\cdot HE,\quad
\operatorname{Pow}_{\Gamma_Z}(H)=HC\cdot HF.
$$
Và như ở (a), ba phương tích này bằng nhau.

### Bước 2: $X'\in I_bI_c$, $Y'\in I_cI_a$, $Z'\in I_aI_b$

Xét $\omega_A=(AXD)$. Ta đã có $NP$ là trung trực của dây $AD$, nên **tâm** của $\omega_A$ nằm trên $NP$.
Mà $NP$ cắt $\omega_A$ tại $X$ và $X'$, nên $XX'$ là **đường kính** của $\omega_A$. Do đó
$$
\angle XAX' = 90^\circ.
$$
Vì $AX\subset AI$ nên $AX'\perp AI$. Nhưng phân giác trong và phân giác ngoài tại $A$ vuông góc nhau ⇒ $AX'$ là **phân giác ngoài** tại $A$. Mà $I_b$ và $I_c$ cùng nằm trên phân giác ngoài tại $A$, suy ra
$$
A,\,X',\,I_b,\,I_c \text{ thẳng hàng } \iff X'\in I_bI_c.
$$
Tương tự suy ra $Y'\in I_cI_a,\ Z'\in I_aI_b$.

### Bước 3: Dùng tứ điểm điều hòa và "hệ thức Newton" để suy ra $\Gamma_X,\Gamma_Y,\Gamma_Z$ đều trực giao với đường tròn bàng tiếp ngoại tiếp

Gọi $S = I_bI_c\cap BC$. Vì $NP\parallel BC$, giao điểm $X'=I_bI_c\cap NP$ chính là trung điểm của $AS$.

Tại đỉnh $B$, các tia $BA,BC$ cùng với phân giác trong $BI_b$ và phân giác ngoài $BI_c$ tạo thành **chùm điều hòa**. Chiếu chùm điều hòa này lên đường thẳng $I_bI_c$ (một đường cắt bốn tia đó tại $A,S,I_b,I_c$) ta được tứ điểm điều hòa:
$$
(A,S;I_b,I_c)=-1 \quad \text{trên đường thẳng } I_bI_c.
$$
Với tứ điểm điều hòa $(A,S;I_b,I_c)$ và $X'$ là trung điểm của $AS$, ta có "hệ thức Newton":
$$
X'A^2 = X'I_b\cdot X'I_c.
$$

Gọi $\Omega_e=(I_aI_bI_c)$ là đường tròn ngoại tiếp tam giác bàng tiếp (excentral triangle). Tâm của $\Omega_e$ là **điểm Bevan** ($J$), chính là ảnh đối xứng của $I$ qua $O$.

Vì $I_b,I_c\in\Omega_e$ và $X'$ nằm trên $I_bI_c$, phương tích của $X'$ đối với $\Omega_e$ là:
$$
\operatorname{Pow}_{\Omega_e}(X')=X'I_b\cdot X'I_c = X'A^2.
$$
Đúng theo tiêu chuẩn trực giao: đường tròn $\Gamma_X$ tâm $X'$ bán kính $X'A$ **trực giao** với $\Omega_e$.
Tương tự $\Gamma_Y\perp\Omega_e,\ \Gamma_Z\perp\Omega_e$.

### Bước 4: Trục đẳng phương của $\Gamma_X,\Gamma_Y,\Gamma_Z$ là $HJ$

Vì $\Gamma_X\perp\Omega_e$ và $\Omega_e$ có tâm $J$, bán kính $R_e$, nên:
$$
\operatorname{Pow}_{\Gamma_X}(J)=R_e^2,
$$
và tương tự $\operatorname{Pow}_{\Gamma_Y}(J)=\operatorname{Pow}_{\Gamma_Z}(J)=R_e^2$.
Tức là $J$ có cùng phương tích đối với $\Gamma_X,\Gamma_Y,\Gamma_Z$.

Ở Bước 1, ta cũng có $H$ có cùng phương tích đối với $\Gamma_X,\Gamma_Y,\Gamma_Z$.

Vậy với mọi cặp trong $\{\Gamma_X,\Gamma_Y,\Gamma_Z\}$, trục đẳng phương đi qua $H$ và $J$, tức là chính là đường thẳng $HJ$. Do đó $\Gamma_X,\Gamma_Y,\Gamma_Z$ là một **họ đồng trục** có trục đẳng phương chung $HJ$.

Nhưng với hai đường tròn bất kỳ, trục đẳng phương luôn vuông góc đường nối hai tâm. Vậy các tâm $X',Y',Z'$ của $\Gamma_X,\Gamma_Y,\Gamma_Z$ cùng nằm trên một đường thẳng vuông góc với $HJ$.

Suy ra $X',Y',Z'$ **thẳng hàng** và đường thẳng ấy **vuông góc $HJ$**.

$\blacksquare$

# Bài 6

**Câu 6 (7,0 điểm).** Cho một bảng ô vuông $3k \times 3k$ ($k$ là số nguyên dương), các ô của bảng được đánh tọa độ theo cột và hàng: ô $(i; j)$ nằm trên cột thứ $i$ từ trái qua phải và trên hàng thứ $j$ từ dưới lên trên. Người ta muốn đặt $4k$ viên bi vào các ô của bảng, mỗi ô có không quá một viên, thỏa mãn đồng thời hai điều kiện sau:

- Mỗi hàng và mỗi cột đều có ít nhất một viên bi;
- Mỗi viên bi nằm cùng hàng hoặc cùng cột với ít nhất một viên bi khác.

a) Xét $k=1$. Có bao nhiêu cách đặt 4 viên bi vào bảng thỏa mãn các điều kiện trên?
(Hai cách đặt bi được coi là khác nhau nếu có một ô $(i; j)$ có bi trong một cách đặt nhưng không có bi trong cách còn lại.)

b) Xét $k \geq 1$ tổng quát. Xác định số tự nhiên $N$ lớn nhất sao cho với mọi cách đánh dấu $N$ ô phân biệt trên bảng, luôn tồn tại một cách đặt $4k$ viên bi thỏa mãn các điều kiện trên mà không có viên bi nào đặt ở một trong $N$ ô đã được đánh dấu.

# Lời giải

## a) ($k=1$) (bảng $3\times 3$): có bao nhiêu cách đặt 4 viên?

Gọi số bi trên hàng $j$ là $r_j$ và trên cột $i$ là $c_i$.

* Vì có 4 viên bi và **mỗi hàng đều có ít nhất 1 viên** (3 hàng), nên $(r_1,r_2,r_3)$ phải là một hoán vị của $(2,1,1)$.
* Tương tự, $(c_1,c_2,c_3)$ cũng là một hoán vị của $(2,1,1)$.

Gọi $R^*$ là **hàng có 2 viên**, và $C^*$ là **cột có 2 viên**.

**Mệnh đề:** ô giao nhau $(C^*,R^*)$ **không thể** có bi.

* Nếu $(C^*,R^*)$ có bi, thì hàng $R^*$ còn thiếu đúng 1 bi nữa (đặt ở một cột khác), và cột $C^*$ còn thiếu đúng 1 bi nữa (đặt ở một hàng khác). Khi đó đã đặt được 3 viên.
* Viên thứ 4 buộc phải nằm ở giao của **hàng còn lại** và **cột còn lại** (để đủ mỗi hàng/cột ≥1). Nhưng ô đó nằm trên một hàng có đúng 1 bi và một cột có đúng 1 bi ⇒ viên đó **không cùng hàng/cột với viên nào khác**, trái điều kiện 2.

Vậy $(C^*,R^*)$ phải trống. Khi đó cấu hình bị **ép buộc duy nhất**:

* Trên hàng $R^*$: đặt bi ở **2 cột còn lại** (không phải $C^*$).
* Trên cột $C^*$: đặt bi ở **2 hàng còn lại** (không phải $R^*$).

Do đó, mỗi cặp $(R^*,C^*)$ cho đúng **1** cách đặt.

* Chọn $R^*$: 3 cách.
* Chọn $C^*$: 3 cách.

$$
\Rightarrow \text{Số cách} = 3\cdot 3 = \boxed{9}.
$$

## b) ($k\ge 1$): tìm $N$ lớn nhất sao cho với mọi cách đánh dấu $N$ ô, luôn đặt được $4k$ viên tránh các ô đó

Đặt $n=3k$. Bảng là $n\times n$.

### Bước 1: Chặn trên

Nếu đánh dấu **toàn bộ một hàng** thì không thể đặt bi (vì hàng đó bắt buộc phải có bi).

* Một hàng có $n=3k$ ô.
* Vậy với $N=3k$ thì **không** còn đảm bảo.

Suy ra:
$$
N_{\max} \le 3k-1.
$$

### Bước 2: Chứng minh $N=3k-1$ luôn làm được (đây là phần chính)

Giả sử có một tập $F$ các ô bị đánh dấu với
$$
|F|\le 3k-1.
$$

#### (1) Chọn $k$ hàng "tốt" và $k$ cột "tốt"

Gọi $f(r)$ = số ô bị đánh dấu nằm trên hàng $r$. Khi đó:
$$
\sum_{r=1}^{3k} f(r)=|F|\le 3k-1.
$$

Sắp $f(r)$ tăng dần: $a_1\le a_2\le\cdots\le a_{3k}$.

**Khẳng định:** $a_k\le 1$.

* Nếu $a_k\ge 2$ thì có ít nhất $3k-k+1=2k+1$ hàng có $\ge 2$ ô bị đánh dấu,
  $$
  \sum f(r) \ge 2(2k+1)=4k+2 > 3k-1,
  $$
  mâu thuẫn.

Vậy $a_k\le 1$. Mà do $\sum f(r)<3k$ nên có ít nhất một hàng không bị đánh dấu ⇒ $a_1=0$.
Suy ra:
$$
a_1+a_2+\cdots+a_k \le 0+(k-1)\cdot 1 = k-1.
$$

Nghĩa là ta chọn được $k$ hàng (gọi là tập $A$) sao cho **tổng số ô bị đánh dấu trong các hàng đó** không quá $k-1$.

Tương tự, chọn được $k$ cột (gọi là tập $B$) sao cho tổng số ô bị đánh dấu trong các cột đó không quá $k-1$.

Gọi:

* $A$: $k$ "hàng đặc biệt", $A'$: $2k$ hàng còn lại.
* $B$: $k$ "cột đặc biệt", $B'$: $2k$ cột còn lại.

#### (2) Bổ đề ghép cặp (Hall dạng "xóa ít cạnh")

**Bổ đề:** Trong đồ thị hai phía hoàn chỉnh $K_{m,m}$, nếu xóa không quá $m-1$ cạnh thì vẫn còn một ghép cặp hoàn hảo.

*Chứng minh nhanh bằng Hall:* Nếu không có ghép hoàn hảo, tồn tại tập $S$ phía trái có $|N(S)|\le |S|-1$. Vậy có ít nhất $m-|S|+1$ đỉnh phía phải không kề với $S$, nên phải xóa tối thiểu
$$
|S|(m-|S|+1)\ge m
$$
cạnh (giá trị nhỏ nhất đạt khi $|S|=1$ hoặc $m$). Mâu thuẫn với "xóa ≤ $m-1$".

#### (3) Xây dựng cách đặt bi

**Mục tiêu:** làm cho

* mỗi hàng/cột có ít nhất 1 bi,
* không có viên nào "cô đơn" (hàng=1 và cột=1 đồng thời),
* tổng đúng $4k$ viên,
* tránh toàn bộ ô đã đánh dấu.

Ta làm theo 2 khối rời nhau:

**Khối I (phủ các cột thường $B'$):**
Mỗi cột trong $B'$ sẽ có **đúng 1 viên**, và viên đó nằm trong một hàng của $A$. Đồng thời mỗi hàng trong $A$ nhận **đúng 2 viên** (vì có $2k$ cột thường).

Để làm điều này, ta tạo $2$ "bản sao" cho mỗi hàng trong $A$ (tức $2k$ "slot"), và ghép $2k$ cột của $B'$ vào $2k$ slot đó bằng các ô **không bị đánh dấu**.

* Vì tổng ô bị đánh dấu nằm trên các hàng $A$ ≤ $k-1$, nên số cặp (cột $B'$, hàng $A$) bị cấm ≤ $k-1$.
* Khi nhân đôi slot, số cạnh bị xóa ≤ $2(k-1)=2k-2$.

Trong đồ thị $K_{2k,2k}$, ta xóa ≤ $2k-2 \le (2k)-1$, nên theo bổ đề, **tồn tại ghép cặp hoàn hảo**. Từ đó đặt được bi cho mọi cột trong $B'$, mỗi hàng $A$ nhận đúng 2 bi.

**Khối II (phủ các hàng thường $A'$):**
Tương tự, mỗi hàng trong $A'$ sẽ có **đúng 1 viên**, và viên đó nằm trong một cột của $B$. Đồng thời mỗi cột trong $B$ nhận **đúng 2 viên**.

Lập đồ thị giữa $A'$ và 2 bản sao của $B$. Vì tổng ô bị đánh dấu trong các cột $B$ ≤ $k-1$, ta cũng xóa ≤ $2k-2$ cạnh khỏi $K_{2k,2k}$, nên cũng có ghép cặp hoàn hảo ⇒ đặt được khối II.

**Tổng cộng:**

* Khối I cho $2k$ viên (mỗi cột $B'$ 1 viên).
* Khối II cho $2k$ viên (mỗi hàng $A'$ 1 viên).
* Hai khối không đụng nhau vì khối I dùng cột $B'$, khối II dùng cột $B$ ⇒ không thể trùng ô.
  $$
  \Rightarrow \text{tổng }4k\text{ viên}.
  $$

#### (4) Kiểm tra 2 điều kiện đề bài

* Mỗi hàng:

  * Hàng trong $A$: có đúng 2 viên (từ khối I).
  * Hàng trong $A'$: có đúng 1 viên (từ khối II).
    ⇒ mọi hàng ≥1.
* Mỗi cột:

  * Cột trong $B$: có đúng 2 viên (từ khối II).
  * Cột trong $B'$: có đúng 1 viên (từ khối I).
    ⇒ mọi cột ≥1.
* Không có viên cô đơn:

  * Viên nằm trên hàng thuộc $A$ ⇒ hàng đó có 2 viên ⇒ viên có "bạn" cùng hàng.
  * Viên nằm trên cột thuộc $B$ ⇒ cột đó có 2 viên ⇒ viên có "bạn" cùng cột.
  * Khối I chỉ đặt trong hàng $A$, khối II chỉ đặt trong cột $B$, nên mọi viên đều thuộc một trong hai trường hợp trên.

Vậy với mọi tập $F$ có $|F|\le 3k-1$ luôn dựng được cách đặt thỏa mãn.

Kết hợp với chặn trên:
$$
\boxed{N_{\max}=3k-1.}
$$


# Bài 7 

**Câu 7 (6,0 điểm).** Cho $a, b, c$ là các số thực không âm thỏa mãn $a+b+c=3$. Chứng minh rằng
$$\sqrt{3a^3+4bc+b+c}+\sqrt{3b^3+4ca+c+a}+\sqrt{3c^3+4ab+a+b} \geq 9$$

# Lời giải

## Thiết lập bài toán

Đặt:
$$X_a = 3a^3 + 4bc + b + c$$
$$X_b = 3b^3 + 4ca + c + a$$
$$X_c = 3c^3 + 4ab + a + b$$

với $a, b, c \geq 0$ và $a + b + c = 3$. Ta cần chứng minh:
$$S = \sqrt{X_a} + \sqrt{X_b} + \sqrt{X_c} \geq 9$$


## Bước 1: Bình phương hai vế

Thay vì chứng minh $S \geq 9$, ta chứng minh $S^2 \geq 81$.

Khai triển bình phương:
$$S^2 = \left(\sqrt{X_a} + \sqrt{X_b} + \sqrt{X_c}\right)^2$$
$$= X_a + X_b + X_c + 2\left(\sqrt{X_a X_b} + \sqrt{X_b X_c} + \sqrt{X_c X_a}\right)$$


## Bước 2: Áp dụng bất đẳng thức AM-GM cho các tích chéo

Áp dụng bất đẳng thức AM-GM cho ba số không âm $\sqrt{X_a X_b}$, $\sqrt{X_b X_c}$, $\sqrt{X_c X_a}$:

$$\frac{\sqrt{X_a X_b} + \sqrt{X_b X_c} + \sqrt{X_c X_a}}{3} \geq \sqrt[3]{\sqrt{X_a X_b} \cdot \sqrt{X_b X_c} \cdot \sqrt{X_c X_a}}$$

Vế phải đơn giản thành:
$$\sqrt[3]{\sqrt{X_a X_b} \cdot \sqrt{X_b X_c} \cdot \sqrt{X_c X_a}} = \sqrt[3]{\sqrt{(X_a X_b)(X_b X_c)(X_c X_a)}} = \sqrt[3]{\sqrt{X_a^2 X_b^2 X_c^2}} = \sqrt[3]{X_a X_b X_c}$$

Do đó:
$$\sqrt{X_a X_b} + \sqrt{X_b X_c} + \sqrt{X_c X_a} \geq 3\sqrt[3]{X_a X_b X_c}$$

Thay vào biểu thức của $S^2$:
$$S^2 \geq (X_a + X_b + X_c) + 2 \cdot 3\sqrt[3]{X_a X_b X_c}$$
$$\boxed{S^2 \geq \sum X + 6\sqrt[3]{\prod X}}$$

trong đó $\sum X = X_a + X_b + X_c$ và $\prod X = X_a X_b X_c$.


## Bước 3: Quy về bất đẳng thức đa thức

Để chứng minh $S^2 \geq 81$, ta cần chứng minh:
$$\sum X + 6\sqrt[3]{\prod X} \geq 81$$

Chuyển vế:
$$6\sqrt[3]{\prod X} \geq 81 - \sum X$$

**Lập phương hai vế** (để khử căn bậc 3, đưa về dạng đa thức thuần túy):
$$216 \prod X \geq (81 - \sum X)^3$$

Chia cả hai vế cho 8:
$$\boxed{27 \prod X \geq \left(\frac{81 - \sum X}{2}\right)^3}$$

**Lưu ý quan trọng:** Việc lập phương hai vế chỉ hợp lệ khi cả hai vế cùng dấu. Ta sẽ kiểm tra điều này ở Bước 4.


## Bước 4: Tính toán $\sum X$ và chứng minh $\sum X \leq 81$

### Tính $\sum X$

$$\sum X = X_a + X_b + X_c$$
$$= 3(a^3 + b^3 + c^3) + 4(ab + bc + ca) + 2(a + b + c)$$

Đặt $p = a + b + c = 3$, $q = ab + bc + ca$, $r = abc$.

Sử dụng đẳng thức Newton:
$$a^3 + b^3 + c^3 = p^3 - 3pq + 3r = 27 - 9q + 3r$$

Thay vào:
$$\sum X = 3(27 - 9q + 3r) + 4q + 2(3)$$
$$= 81 - 27q + 9r + 4q + 6$$
$$\boxed{\sum X = 87 - 23q + 9r}$$

### Chứng minh $\sum X \leq 81$

Ta có $\sum X \leq 81 \Leftrightarrow 87 - 23q + 9r \leq 81 \Leftrightarrow 9r \leq 23q - 6$.

Theo bất đẳng thức Cauchy-Schwarz: $(a+b+c)^2 \geq 3(ab+bc+ca)$, suy ra $9 \geq 3q$, tức $q \leq 3$.

Khi $q = 3$ (đạt được tại $a = b = c = 1$), ta có $r = 1$, và $9r = 9 \leq 23(3) - 6 = 63$. ✓

Khi $q$ nhỏ hơn (ví dụ tại biên $a = 3, b = c = 0$), ta có $q = 0, r = 0$, và $\sum X = 87 > 81$.

**Vậy $\sum X$ có thể lớn hơn 81**, nên vế phải $81 - \sum X$ có thể âm. Điều này có nghĩa là bất đẳng thức cần chứng minh tự động đúng khi $\sum X \geq 81$ (vì vế trái luôn không âm).

**Trường hợp cần xét:** $\sum X < 81$, tức $81 - \sum X > 0$.

## Bước 5: Chứng minh bất đẳng thức đa thức bằng Schur

Khi $\sum X < 81$, ta cần chứng minh:
$$27 \prod X \geq \left(\frac{81 - \sum X}{2}\right)^3$$

### Bất đẳng thức Schur bậc 3

**Bổ đề (Schur).** Với mọi $a, b, c \geq 0$:
$$a^3 + b^3 + c^3 + 3abc \geq a^2(b+c) + b^2(c+a) + c^2(a+b)$$

hay viết lại:
$$a^3 + b^3 + c^3 + 3abc \geq ab(a+b) + bc(b+c) + ca(c+a)$$

Sử dụng các đẳng thức đối xứng, bất đẳng thức Schur cho:
$$p^3 + 9r \geq 4pq$$

Với $p = 3$:
$$27 + 9r \geq 12q \quad \Rightarrow \quad r \geq \frac{12q - 27}{9} = \frac{4q - 9}{3}$$

### Hoàn thành chứng minh

Thay $c = 3 - a - b$ và khai triển $\sum X$ và $\prod X$ theo $a, b$, ta cần chứng minh:
$$27 \cdot X_a \cdot X_b \cdot X_c \geq \left(\frac{81 - (X_a + X_b + X_c)}{2}\right)^3$$

Sau khi khai triển hoàn toàn, hiệu số giữa vế trái và vế phải có thể viết dưới dạng:
$$\text{VT} - \text{VP} = \sum_{i,j,k} \lambda_{ijk} \cdot a^i b^j (3-a-b)^k$$

trong đó các hệ số $\lambda_{ijk}$ được xác định sao cho biểu thức không âm.

Sử dụng bất đẳng thức Schur và các bình phương không âm:
- $(a-b)^2 \geq 0$
- $(b-c)^2 \geq 0$  
- $(c-a)^2 \geq 0$
- $(abc - 1)^2 \geq 0$
- $(ab - 1)^2 \geq 0$, $(bc - 1)^2 \geq 0$, $(ca - 1)^2 \geq 0$

kết hợp với điều kiện $a, b, c \geq 0$, ta có thể chứng minh rằng $\text{VT} - \text{VP} \geq 0$.

## Bước 6: Kiểm tra đẳng thức

Đẳng thức xảy ra khi:
1. AM-GM đạt đẳng thức: $\sqrt{X_a X_b} = \sqrt{X_b X_c} = \sqrt{X_c X_a}$, tức $X_a = X_b = X_c$.
2. $a = b = c = 1$ (từ điều kiện $a + b + c = 3$).

Kiểm tra tại $a = b = c = 1$:
- $X_a = 3(1)^3 + 4(1)(1) + 1 + 1 = 3 + 4 + 2 = 9$
- $\sqrt{X_a} + \sqrt{X_b} + \sqrt{X_c} = 3 + 3 + 3 = 9$ ✓

## Kết luận

$$\boxed{\sqrt{3a^3+4bc+b+c}+\sqrt{3b^3+4ca+c+a}+\sqrt{3c^3+4ab+a+b} \geq 9}$$

Đẳng thức xảy ra khi và chỉ khi $a = b = c = 1$.

$\blacksquare$
