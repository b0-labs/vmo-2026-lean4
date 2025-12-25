# BÀI 1

Với mỗi số nguyên dương $n$, xét
$$
P_n(x)=x^{3n}-3\cdot 4^{\,n-1}x^n-2^{3n-3}.
$$

**a)** Chứng minh $P_n(x)$ có đúng một nghiệm thực dương, kí hiệu $a_n$.

**b)** Đặt $\displaystyle b_n=\frac{2-a_n}{n}$ và $\displaystyle c_n=b_1+b_2+\cdots+b_n$. Chứng minh $(c_n)$ có giới hạn hữu hạn.

# Lời giải
## a) $P_n(x)$ có đúng một nghiệm dương

Đặt
$$
t=\left(\frac{x}{2}\right)^n \quad (x>0 \iff t>0).
$$
Khi đó $x^n=2^n t$ và $x^{3n}=2^{3n}t^3$. Thế vào $P_n(x)$:

* Hạng đầu: $x^{3n}=2^{3n}t^3$.
* Hạng giữa:
  $$
  3\cdot 4^{n-1}x^n = 3\cdot 2^{2n-2}\cdot 2^n t = 3\cdot 2^{3n-2}t.
  $$
* Hằng số: $2^{3n-3}$.

Vậy
$$
P_n(x)=2^{3n}t^3-3\cdot 2^{3n-2}t-2^{3n-3}
=2^{3n-3}\bigl(8t^3-6t-1\bigr).
$$

Đặt
$$
Q(t)=8t^3-6t-1.
$$
Ta có với mọi $x>0$:
$$
P_n(x)=0 \iff Q\!\left(\left(\frac{x}{2}\right)^n\right)=0.
$$

Như vậy, số nghiệm dương của $P_n$ đúng bằng số nghiệm dương của $Q$, vì ánh xạ
$$
x\mapsto \left(\frac{x}{2}\right)^n
$$
là **song ánh tăng** từ $(0,\infty)$ sang $(0,\infty)$.

Xét đạo hàm:
$$
Q'(t)=24t^2-6=6(4t^2-1).
$$
Suy ra:

* $Q'(t)<0$ khi $0<t<\frac12$  $\Rightarrow Q$ **giảm** trên $\left(0,\frac12\right)$.
* $Q'(t)>0$ khi $t>\frac12$ $\Rightarrow Q$ **tăng** trên $\left(\frac12,\infty\right)$.

Tính giá trị:
$$
Q\!\left(\frac12\right)=8\cdot\frac18-6\cdot\frac12-1=1-3-1=-3<0,
$$
$$
Q(1)=8-6-1=1>0.
$$
Vì $Q$ tăng trên $\left(\frac12,\infty\right)$ và đổi dấu từ âm sang dương trên $\left(\frac12,1\right)$, nên $Q$ có **đúng một nghiệm dương** $t_0\in\left(\frac12,1\right)$.

Vì $x\mapsto\left(\frac{x}{2}\right)^n$ là song ánh tăng trên $(0,\infty)$, từ
$$
P_n(x)=0 \iff Q\!\left(\left(\frac{x}{2}\right)^n\right)=0
$$
suy ra $P_n$ có **đúng một nghiệm dương**, ký hiệu $a_n$, và nghiệm đó thỏa
$$
\left(\frac{a_n}{2}\right)^n=t_0
\quad\Longrightarrow\quad
a_n=2\,t_0^{1/n}.
$$

*(Ghi chú : từ $Q(t)=0 \iff 4t^3-3t=\tfrac12$, dùng công thức $\cos 3\theta=4\cos^3\theta-3\cos\theta$ suy ra nghiệm dương là $t_0=\cos\frac{\pi}{9}$. Khi đó $a_n=2\cos^{1/n}\!\frac{\pi}{9}$. Không bắt buộc, nhưng hữu ích cho (b).)*

## b) Dãy $(c_n)$ có giới hạn hữu hạn

Từ (a) ta có
$$
a_n=2\,t_0^{1/n},
\quad \text{với } t_0\in\left(\frac12,1\right).
$$
Do $0<t_0<1$ nên $t_0^{1/n}<1$, suy ra $a_n<2$ và
$$
b_n=\frac{2-a_n}{n}
=\frac{2-2t_0^{1/n}}{n}
=\frac{2(1-t_0^{1/n})}{n} >0.
$$
Vì $b_n>0$ nên $(c_n)$ tăng.

Ta cần chứng minh $(c_n)$ bị chặn trên.

Đặt
$$
t_0=e^{-s}\quad (s=-\ln t_0>0).
$$
Khi đó
$$
t_0^{1/n}=e^{-s/n}.
$$
Suy ra
$$
b_n=\frac{2(1-e^{-s/n})}{n}.
$$

Dùng bất đẳng thức cơ bản $e^x\ge 1+x$ (đúng với mọi $x\in\mathbb R$). Thay $x=-\frac{s}{n}$ ta được
$$
e^{-s/n}\ge 1-\frac{s}{n}
\quad\Longrightarrow\quad
1-e^{-s/n}\le \frac{s}{n}.
$$
Do đó
$$
0<b_n=\frac{2(1-e^{-s/n})}{n}\le \frac{2\cdot (s/n)}{n}=\frac{2s}{n^2}.
$$

Vì $\sum_{n=1}^\infty \frac{1}{n^2}$ hội tụ, nên theo so sánh:
$$
\sum_{n=1}^\infty b_n
\quad \text{hội tụ (vì } b_n\le \frac{2s}{n^2}\text{)}.
$$
Mà $c_n=\sum_{k=1}^n b_k$ là tổng từng phần của một chuỗi hội tụ, nên $c_n$ có giới hạn hữu hạn.

Thậm chí ta có chặn trên cụ thể:
$$
c_n=\sum_{k=1}^n b_k
\le 2s\sum_{k=1}^n \frac1{k^2}
\le 2s\cdot \frac{\pi^2}{6}<\infty.
$$

Vậy $(c_n)$ **tăng và bị chặn trên**, nên **hội tụ** $\Rightarrow$ có giới hạn hữu hạn.

# Bài 2 

**Câu 2 (5 điểm).** Để khám phá không gian, các nhà khoa học thường phải quan sát những vật thể xa xôi như sao chổi, tiểu hành tinh và các hiện tượng thiên văn khác. Nhằm mục đích đó, các nhà khoa học thiết kế và phóng các vệ tinh quan sát lên quỹ đạo quanh Trái Đất. Hầu hết các vệ tinh không chuyển động theo vòng tròn hoàn hảo mà có quỹ đạo là một đường elip, với Trái Đất nằm ở một trong hai tiêu điểm của elip. Khi một vệ tinh chuyển động trên quỹ đạo elip, khoảng cách giữa nó và vật thể cần quan sát liên tục thay đổi. Thông thường, nếu khoảng cách từ vệ tinh đến vật thể cần quan sát là ngắn nhất thì các thiết bị cảm biến trên vệ tinh sẽ nhận được tín hiệu tốt nhất.

Cho một vệ tinh (được xem như là một chất điểm) chuyển động xung quanh Trái Đất theo quỹ đạo là một đường elip. Trong không gian với hệ trục tọa độ vuông góc $Oxyz$ (đơn vị trên mỗi trục $Ox, Oy, Oz$ đều bằng 6400 km), giả sử vệ tinh chuyển động trên mặt phẳng tọa độ $(Oxy)$ theo quỹ đạo có phương trình là $x^2+3y^2=17$. Vệ tinh cần quan sát một vật thể (cũng được xem như là một chất điểm) chuyển động trong không gian. Theo các kết quả nghiên cứu, khi vật thể chuyển động đến vị trí $A\left(2; \frac{16}{\sqrt{3}}; 8\right)$ thì việc quan sát vật thể đó là tốt nhất. Hãy xác định tọa độ điểm $C$ (trên quỹ đạo elip của vệ tinh) trong không gian với hệ trục tọa độ $Oxyz$ nói trên sao cho khoảng cách từ vị trí $C$ đến vị trí $A$ là ngắn nhất.

# Lời giải

Gọi $C(x,y,z)$ là vị trí của vệ tinh trên quỹ đạo. Vì vệ tinh chuyển động trong mặt phẳng $(Oxy)$ nên

$$ z=0,\qquad x^2+3y^2=17. $$

Điểm cần quan sát là $A\left(2,\dfrac{16}{\sqrt3},8\right)$.

Khoảng cách bình phương:

$$ AC^2=(x-2)^2+\left(y-\frac{16}{\sqrt3}\right)^2+(0-8)^2 = \underbrace{(x-2)^2+\left(y-\frac{16}{\sqrt3}\right)^2}_{=:F(x,y)}+64. $$

Vì $64$ là hằng số, việc **tối thiểu hóa** $AC$ tương đương với tối thiểu hóa $$ F(x,y)=(x-2)^2+\left(y-\frac{16}{\sqrt3}\right)^2 $$ với ràng buộc $g(x,y)=x^2+3y^2-17=0$.

Ta có $$ \nabla F=(2(x-2),,2(y-\tfrac{16}{\sqrt3})),\qquad \nabla g=(2x,,6y). $$

Điều kiện Lagrange: $\nabla F=\lambda \nabla g$, tức là 

$$
\left\{\begin{array} { l } 
{ 2 ( x - 2 ) = \lambda \cdot 2 x } \\
{ 2 ( y - \frac { 1 6 } { \sqrt { 3 } } ) = \lambda \cdot 6 y } \\
{ x ^ { 2 } + 3 y ^ { 2 } = 1 7 }
\end{array} \Longleftrightarrow \left\{\begin{array}{l}
x-2=\lambda x \\
y-\frac{16}{\sqrt{3}}=3 \lambda y \\
x^2+3 y^2=17 .
\end{array}\right.\right.
$$

Từ hai phương trình đầu: $$ x(1-\lambda)=2 \Rightarrow x=\frac{2}{1-\lambda},\qquad y(1-3\lambda)=\frac{16}{\sqrt3}\Rightarrow y=\frac{16/\sqrt3}{1-3\lambda}. $$
Thử $\lambda=-1$:

$$ x=\frac{2}{1-(-1)}=\frac{2}{2}=1,\qquad y=\frac{16/\sqrt3}{1-3(-1)}=\frac{16/\sqrt3}{4}=\frac{4}{\sqrt3}. $$

Kiểm tra thuộc elip: $$ x^2+3y^2=1^2+3\left(\frac{4}{\sqrt3}\right)^2 =1+3\cdot \frac{16}{3}=1+16=17 \quad\Rightarrow\quad C\in {x^2+3y^2=17}. $$
Vậy ta có ứng viên $$ C_1\left(1,\frac{4}{\sqrt3},0\right). $$

Do elip là đường cong đóng (compact), hàm $AC$ liên tục nên **tồn tại** điểm gần $A$ nhất trên elip. Các điểm cực trị chỉ có thể là nghiệm hệ Lagrange; kiểm tra (bằng Sympy ở phần dưới) cho thấy chỉ có **2 nghiệm thực**, trong đó $C_1$ cho giá trị $AC$ nhỏ hơn nên chính là nghiệm cực tiểu.

Tính khoảng cách tại $C_1$: $$ AC_1^2=(1-2)^2+\left(\frac{4}{\sqrt3}-\frac{16}{\sqrt3}\right)^2+(0-8)^2 =1+\left(-\frac{12}{\sqrt3}\right)^2+64 =1+\frac{144}{3}+64=113. $$ $$ \Rightarrow\quad AC_{\min}=\sqrt{113}. $$

Điểm $C$ trên quỹ đạo elip sao cho khoảng cách đến $A$ nhỏ nhất là

$$ \boxed{C\left(1,\frac{4}{\sqrt3},0\right).} $$

Nếu đổi ra km (vì 1 đơn vị trục = 6400 km), thì $$ \boxed{C=\left(6400,\ \frac{25600}{\sqrt3},\ 0\right)\ \text{km}.} $$
# Bài 3

Cho $(n,a,b)$ là các số nguyên dương thỏa mãn
$$
1<n^2<a<b<n^2+n+3.
$$
Tìm **tất cả các ước nguyên dương** của $ab$ **nằm trong khoảng** $(n^2,\;n^2+n+3)$.
# Lời giải

Vì $1<n^2$ nên $n\ge 2$.

Khoảng $(n^2,\;n^2+n+3)$ chứa đúng các số nguyên
$$
n^2+1,\;n^2+2,\;\dots,\;n^2+n+2.
$$

Đặt
$$
a=n^2+x,\qquad b=n^2+y
$$
với
$$
1\le x<y\le n+2.
$$

Xét một ước dương $d$ của $ab$ sao cho
$$
n^2<d<n^2+n+3.
$$
Khi đó cũng có dạng
$$
d=n^2+z\qquad \text{với }1\le z\le n+2.
$$
Vì $d\mid ab$ nên
$$
n^2+z \mid (n^2+x)(n^2+y).
$$
Lấy modulo $n^2+z$ ta có $n^2\equiv -z$, do đó
$$
(n^2+x)(n^2+y)\equiv (x-z)(y-z)\pmod{n^2+z}.
$$
Suy ra
$$
n^2+z \mid (x-z)(y-z). \tag{1}
$$

Vì $x,y,z\in[1,n+2]$ nên
$$
|x-z|\le n+1,\qquad |y-z|\le n+1
$$
nên
$$
|(x-z)(y-z)|\le (n+1)^2. \tag{2}
$$

Mặt khác, với $n\ge 2$ và $z\ge 1$,
$$
2(n^2+z) - (n+1)^2 \;\ge\; 2(n^2+1)-(n+1)^2
=2n^2+2-(n^2+2n+1)
=(n-1)^2>0.
$$
Suy ra
$$
(n+1)^2 < 2(n^2+z)=2d. \tag{3}
$$

Từ (2) và (3):
$$
|(x-z)(y-z)| < 2d.
$$

Kết hợp với (1): nếu một bội của $d$ có trị tuyệt đối nhỏ hơn $2d$ thì bội đó chỉ có thể là
$$
0,\;d,\;\text{hoặc }-d.
$$
Do đó
$$
(x-z)(y-z)\in\{0,\;d,\;-d\}. \tag{4}
$$
**(i) Nếu $(x-z)(y-z)=0$**

Thì $z=x$ hoặc $z=y$. Khi đó
$$
d=n^2+z = n^2+x=a \quad\text{hoặc}\quad d=n^2+y=b.
$$
Tức là $d\in\{a,b\}$.

**(ii) Nếu $(x-z)(y-z)=\pm d$**

Lấy trị tuyệt đối, đặt
$$
u=|x-z|,\quad v=|y-z|
$$
thì $1\le u,v\le n+1$ và
$$
uv = d = n^2+z > n^2. \tag{5}
$$
Nếu $u\le n$ và $v\le n$ thì $uv\le n^2$, trái với (5). Vậy **ít nhất một** trong $u,v$ bằng $n+1$. Suy ra
$$
n+1 \mid uv = n^2+z \quad\Rightarrow\quad n+1 \mid (n^2+z). \tag{6}
$$

Mà $n^2 \equiv 1 \pmod{n+1}$ (vì $n\equiv -1\pmod{n+1}$), nên từ (6):
$$
n^2+z \equiv 1+z \equiv 0 \pmod{n+1}
\Rightarrow z\equiv -1 \pmod{n+1}.
$$
Với $1\le z\le n+2$, nghiệm duy nhất là $z=n$.
Suy ra
$$
d=n^2+z = n^2+n = n(n+1).
$$
Khi đó từ $uv=d$ và một trong $u,v$ bằng $n+1$, số còn lại phải bằng $n$. Nên
$$
\{u,v\}=\{n,\;n+1\}.
$$
Đặc biệt có $u=n+1$ hoặc $v=n+1$, tức là
$$
|x-n|=n+1 \quad\text{hoặc}\quad |y-n|=n+1.
$$
Nhưng $1\le x,y\le n+2$ nên
$$
|x-n|\le \max(n-1,2) < n+1,\qquad |y-n|\le \max(n-1,2) < n+1,
$$
mâu thuẫn. Vậy trường hợp $\pm d$ **không thể xảy ra**.

Kết luận: mọi ước $d$ của $ab$ nằm trong $(n^2,\;n^2+n+3)$ đều phải là $a$ hoặc $b$. Và hiển nhiên $a\mid ab$, $b\mid ab$, nên chúng đều xuất hiện.

$$
\boxed{\text{Các ước dương của }ab\text{ nằm trong }(n^2,\;n^2+n+3)\text{ là đúng hai số }a\text{ và }b.}
$$
# Bài 4 

**Câu 4 (5 điểm).** Bạn An chơi trò chơi ghi lên bảng các bộ ba số theo thứ tự từ trái sang phải. Ban đầu trên bảng ghi sẵn bộ ba số $(1,1,1)$. Ở mỗi lượt chơi, An thực hiện một trong hai thao tác sau với bộ ba số $(x, y, z)$ hiện có:

(i) Xóa bộ ba số $(x, y, z)$ và viết lên bảng bộ ba số $(y, z, x+z)$.

(ii) Xóa bộ ba số $(x, y, z)$ và viết lên bảng bộ ba số $(x+z+1, x+y+z+1, x+y+2z+1)$.

a) Chứng minh An cần đúng 4 lượt chơi để có thể viết lên bảng bộ ba số $(a, b, 6)$.

b) Tìm số tự nhiên $k$ nhỏ nhất sao cho tồn tại một cách chơi để sau $k$ lượt, An có thể viết lên bảng bộ ba số $(c, d, 129)$.

# Lời giải

Cho

* **(i)** $(A(x,y,z)=(y,\;z,\;x+z))$
* **(ii)** $(B(x,y,z)=(x+z+1,\;x+y+z+1,\;x+y+2z+1))$

Bắt đầu từ $(1,1,1)$.
## Quan sát then chốt: (ii) là "ba lần (i), rồi +1"

Áp dụng (i) ba lần cho $(x,y,z)$:

* Sau 1 lần:
  $$
  A(x,y,z)=(y,z,x+z)
  $$
* Sau 2 lần:
  $$
  A^2(x,y,z)=A(y,z,x+z)=(z,\;x+z,\;y+(x+z))=(z,\;x+z,\;x+y+z)
  $$
* Sau 3 lần:
  $$
  A^3(x,y,z)=A(z,\;x+z,\;x+y+z)=(x+z,\;x+y+z,\;z+(x+y+z))=(x+z,\;x+y+z,\;x+y+2z)
  $$

Do đó
$$
B(x,y,z)=A^3(x,y,z) + (1,1,1).
$$
Đẳng thức này là động cơ của lời giải.

## Định nghĩa dãy "thuần (A)" cho tọa độ thứ 3

Đặt
$$
A^n(1,1,1)=(*,*,u_n),
$$
vậy $u_n$ là số thứ ba sau khi thực hiện phép toán (i) đúng $n$ lần.

Từ $A(x,y,z)=(y,z,x+z)$, nếu ta áp dụng $A$ liên tục, tọa độ thứ ba thỏa mãn
$$
u_{n+3}=u_{n+2}+u_n
$$
(vì mỗi số hạng thứ ba mới là "số thứ nhất cũ + số thứ ba cũ", và đó là $u_n$ và $u_{n+2}$ trong cách đánh chỉ số này).

Tính các giá trị ban đầu:

* $A^0(1,1,1)=(1,1,1)\Rightarrow u_0=1$
* $A^1(1,1,1)=(1,1,2)\Rightarrow u_1=2$
* $A^2(1,1,1)=(1,2,3)\Rightarrow u_2=3$

Bây giờ sử dụng $u_{n+3}=u_{n+2}+u_n$:

$$
\begin{aligned}
u_3&=u_2+u_0=3+1=4\\
u_4&=u_3+u_1=4+2=6\\
u_5&=u_4+u_2=6+3=9\\
u_6&=u_5+u_3=9+4=13\\
u_7&=u_6+u_4=13+6=19\\
u_8&=u_7+u_5=19+9=28\\
u_9&=u_8+u_6=28+13=41\\
u_{10}&=u_9+u_7=41+19=60\\
u_{11}&=u_{10}+u_8=60+28=88\\
u_{12}&=u_{11}+u_9=88+41=129
\end{aligned}
$$

Cũng nhận thấy ngay:
$$
u_{n+3}-u_{n+2}=u_n>0 \quad\Rightarrow\quad (u_n)\ \text{tăng ngặt.}
$$
## Bổ đề cấu trúc cho mọi cách chơi hỗn hợp

Giả sử sau **k** lượt chơi, bạn đã sử dụng phép toán **(ii)** đúng **m** lần.

Vì $B = A^3 + (1,1,1)$, mỗi lần bạn sử dụng $B$ bạn:

1. áp dụng $A^3$ (ba "bước-$A$"), và
2. thêm một $(1,1,1)$ bổ sung, sau đó được biến đổi bởi các bước $A$ tiếp theo.

Vậy sau tất cả các lượt chơi, bộ ba cuối cùng có thể được viết là
$$
A^{\,N}(1,1,1)\;+\;\sum_{j=1}^m A^{t_j}(1,1,1)
$$
với một số nguyên $t_1>\cdots>t_m\ge 0$, trong đó
$$
N = (k-m)\cdot 1 + m\cdot 3 = k+2m,
$$
và hơn nữa các số mũ thỏa mãn điều kiện khoảng cách quan trọng
$$
t_{j} \ge t_{j+1}+3.
$$
Lý do: giữa hai phép cộng "$(+ (1,1,1))$" có ít nhất phần $A^3$ của $B$ tiếp theo, tức là ít nhất 3 bước-$A$.

Chỉ lấy **tọa độ thứ ba**, điều này trở thành
$$
z = u_{N} + \sum_{j=1}^m u_{t_j}
\qquad\text{với } N=k+2m,\ t_j\ge t_{j+1}+3.
$$

## (a) Chứng minh An cần **đúng 4 lượt chơi** để đạt được $(a,b,6)$ nào đó

Sử dụng phép toán (i) bốn lần:

$$
(1,1,1)\xrightarrow{(i)}(1,1,2)\xrightarrow{(i)}(1,2,3)\xrightarrow{(i)}(2,3,4)\xrightarrow{(i)}(3,4,6).
$$

Vậy sau 4 lượt chơi ta có thể viết $(a,b,6)$, ví dụ $(3,4,6)$.

Giả sử ta đạt được tọa độ thứ ba $z=6$ trong $k\le 3$ lượt chơi.

* Nếu $m=0$ (không có phép toán (ii)), thì $z=u_k\le u_3=4$, không thể.
* Nếu $m\ge 1$, thì $N=k+2m\ge k+2\ge 3$. Thực tế với $k\le3$, nhỏ nhất có thể là $k=1,m=1\Rightarrow N=3$.
  Sử dụng bổ đề,
  $$
  z = u_N + \sum_{j=1}^m u_{t_j}\ge u_N + 1.
  $$
  Nếu $k=3,m=1$ thì $N=5\Rightarrow z\ge u_5+1=9+1=10>6$.
  Nếu $k=2,m=1$ thì $N=4\Rightarrow z\ge u_4+1=6+1=7>6$.
  Nếu $k=1,m=1$ thì $N=3\Rightarrow z=u_3+u_0=4+1=5\neq 6$.

Vậy $z=6$ không thể xảy ra trong $\le 3$ lượt chơi.

Do đó, số tối thiểu là **đúng $4$**.

## (b) Tìm $k$ nhỏ nhất sao cho sau $k$ lượt chơi ta có thể đạt được $(c,d,129)$

### Tồn tại với $k=12$

Ta đã tính $u_{12}=129$. Chỉ sử dụng phép toán (i) 12 lần cho tọa độ thứ ba là $129$.
Thực tế, tiếp tục dãy $A$ ta được:
$$
A^{12}(1,1,1)=(60,88,129),
$$
vậy $(c,d)=(60,88)$ thỏa mãn.

Do đó $k\le 12$.

Giả sử ta có thể đạt được $z=129$ trong $k\le 11$ lượt chơi.

* Nếu $m=0$, thì $z=u_k\le u_{11}=88$, mâu thuẫn.
  Vậy ta phải có $m\ge 1$.

Đặt $N=k+2m$. Khi đó theo bổ đề:
$$
129 = z = u_N + \sum_{j=1}^m u_{t_j},
\quad t_j\ge t_{j+1}+3.
$$

Nếu $N\ge 12$, thì $u_N\ge u_{12}=129$, và vì $m\ge1$ nên tổng $\sum u_{t_j}\ge 1$, cho $z>129$, không thể.
Vậy $N\le 11$, do đó $u_N\le u_{11}=88$. Vì vậy "phần bổ sung" phải là
$$
\sum_{j=1}^m u_{t_j} = 129-u_N \ge 129-88=41.
\tag{★}
$$

Bây giờ sử dụng khoảng cách và sự kiện $t_1\le N-3\le 8$:

* Nếu $m=1$: thì $t_1\le 8$, vậy
  $$
  \sum u_{t_j} = u_{t_1}\le u_8 = 28 < 41,
  $$
  mâu thuẫn với (★).

* Nếu $m=2$: thì $t_1\le 8$ và $t_2\le t_1-3\le 5$, vậy
  $$
  \sum u_{t_j}\le u_8+u_5 = 28+9=37 < 41,
  $$
  mâu thuẫn.

* Nếu $m=3$: thì $t_1\le 8$, $t_2\le 5$, $t_3\le 2$, vậy
  $$
  \sum u_{t_j}\le u_8+u_5+u_2 = 28+9+3=40 < 41,
  $$
  mâu thuẫn.

Ngoài ra, $m\ge 4$ là không thể khi $N\le 11$ vì mỗi $B$ đóng góp 3 bước-$A$, vậy $3m\le N\le 11\Rightarrow m\le 3$.

Vậy không trường hợp nào thỏa mãn: **bạn không thể đạt được $z=129$ trong $k\le 11$ lượt chơi**.

Do đó số tối thiểu là
$$
\boxed{k=12.}
$$