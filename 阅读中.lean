正在阅读Adventures in group theory Rubiks cube,
    Merlins machine, and other mathematical toys (Joyner, David) --ok
看完第5章，--doing 1.一组魔方操作，最多重复操作1260次就可以还原，不多吧，操作为m = RU2D−1BD−1 。柯西定理有此话题更多的讨论。 --ok
还是得从书的第一页开始，不懂的举例子|然后要将关键定理用我们自己的理解记下来，不然会忘|跳过非魔方的部分--ok
|定理不一定要详细证明，但是名词一定要彻底理解，这样证明就只是一种技巧 ｜写记录的时候先写个总概括--ok

实在不懂的找gpt举例子：
关键定理自我理解记录：
1.P (f ) :是一个矩阵，其中 f 是一个排列，举例；
    写成f=（2，1，3）， P(f)就是
   [[0 1 0]
    [1 0 0]
    [0 0 1]], 也就是第1行第2列，第2行第1列，第3行第3列，根据f来的，都是1，其他为0
2.Sn : 有时代表任意排列组成的集合，元素数量当然就是n!个
3.与有关的魔方引理lemma 3.2.3：r^−1sr复合操作，能直接修改首位位置，修改效果是直接通过r映射。
    举例：
    i是uf位置,j是uf位置
    有一个操作s效果是3循环：s:= uf → ul → ur → uf ,
    另一个操作r := F^2
    则：
    r^−1sr的效果是r(i)位置 → r(j)位置
    因为r(uf)= df,所以：
    df → ul → ur → df
4.对于排列f，f的order定义:使得 f^N = 1 > 0 的最小整数 N 称为 f 的阶数order
5.对于排列f，f是even或odd的，意思是：swap(f ) 是even或odd，也就是f的逆序数之和
    逆序数具体定义：
    定义 3.1.1. 让 f : 跟n → 跟n 是一个排列组合，让
    和f (i) = #{j > i | f (i) > f (j)}, 1 ≤ i ≤ n − 1.
    swap（f ) = 和f (1) + . . . + 和f (n − 1)
6.算法：生成所有排列的方式竟然如此简单 3.4
7.超级翻转游戏：只翻转所有棱块，其他角块和中心块不影响
8.Sn ：对于集合n，任意排列(一个排列可以用一个向量来表示)组成的集合,也可以记为“symmetric对称群”，
    因为满足P87的四个属性：封闭+结合律+单位排列+逆排列。
    symmetric：是群A的一个可选性质，群A需满足：封闭+结合律+单位排列+逆排列。
    比如对于集合N={1,2,3},N中元素任意排列得到若干向量g1,g2,...gm ，有这些向量g1,g2,...gm组成的集合，满足群的定义，且满足四个属性，所以具备symmetric这个群的可选性质。
9.tips:从群的乘法表出发分析，可以很容易的定义和判别是否阿贝尔群，关于对角线对称。
10.由某个集合S生成的置换群G，定义是:由某个有限的集合S，S集合里面元素是一个个排列，
    这样来定义置换群G：G集合需要满足：里面元素是任意S里面的元素复合运算得到的结果（当然也是一个个排列）。
11.魔方群：是一个置换群G，也叫做由Sx中的元素“生成”的置换群。
    X： 是魔方的 54 个面的集合，
    Sx：是一个排列的集合，让 R、L、U、D、F、B ∈ Sx 表示魔方的基本动作， R、L、U、D、F、B都是一个个排列
    置换群G = <R、L、U、D、F、B> ⊂ Sx 就称作魔方群（每一个状态，是由某一组操作来代表的）
12.对于群G，群G的order，符号|G|表示： 群元素的数量。 魔方群的|G| = 2^27*3^14*5^3*7^2*11
13.对于群的元素g，g的order，符号ord(g)表示：使得g^m=1 的最小的m（如果m存在的话）.
    魔方群中最大order为元素m = RU2D−1BD−1，其order为1260
14.柯西定理，用来判断元素g，g满足order是某个数，这样的g，是否存在。
    因此可以判断魔方群中某个元素g,g符合order为某个值，能判断这样的g是否能存在。
15.对于群G，群G由一个元素A通过运算生成的，称为cyclic 循环的群。换句话说，G中元素都是这样的一般形式：A^k , k=1,2,3...
16.对于群G，和G的子群H，这样的数|G|/|H|， 称为index ，符号记为[G:H]。
17.对于群G，G的center，中心：center是一个G的子群，里面的元素z，对于任意的群G里面的元素g，z ∗ g = g ∗ z，换句话说可以左乘+右乘相等的
    具体集合定义为Z（G） = {z ∈ G | z ∗ g = g ∗ z，对于所有 g ∈ G}。
    trivial center：当子群Z（G）只有一个元素时，这个元素也就是最普通的单位元时，就称作平凡的。
    借此机会，对于群G，可以定义commutative：群G，如果G = Z（G），即G等于G的这个子群，则G称作交换的。
18.对于魔方群G，G是S₄₈（一个由48元素的任意排列，这样的排列为元素组成的群）的一个子群。
19.对于魔方群G，G的center就是集合Z(G) = {1, superflip}
    superflip已被人们所知道的一个是：
    superflip = R · L · F · B · U · D · R · L · F · B · U · F 2 · M R ·
    ·F 2 · U −1 · MR 2
    R · B2 · MR −1
    R · B2 · U · MR 2
    R · D
    = R · L · F · B · U · D · R · L · F · B · U · F 2 · R−1 ·
    ·L · D2 · F −1 · R2 · L2 · D2 · R · L−1 ·
    ·F 2 · D · R2 · L2 · D (34 quarter turns)（它是34次转动的一组操作）
    （这里MR 指的是右中间切片顺时针旋转 90 度（从右边的面来看））
    而且已被证明，最小转动次数的superflip是一下这个：
    R, R−1 , L, L−1 , U, U −1 , D, D−1 , B, B−1 , F, F −1
20.由魔方的两个2次操作组成的群H：H = 〈R^2, U^2〉,
    这个群的所有12个元素是：
    H = {1, R2 , R2 · U2 , R2 · U2 · R2 ,(R2 · U2 )^2 ,(R2 · U2 )^2 · R2 ,(R2 · U2 )^3 ,
        (R2 · U2 )^3 · R2 ,(R2 · U2 )4 ,(R2 · U2 )^4 · R2 ,(R2 · U2 )^5 ,(R2 · U2 )^5 · R2 }
    单位元满足：1 = （R2 · U2 )^6
21.对于群G，g、h是G中的元素，commutator of g,h：是一个G中的元素，记为[g,h]，[g,h] = g ∗ h ∗ g−1 ∗ h−1
    讲一个常识：先穿袜子再穿鞋，和，先穿鞋再穿袜子，不一样！！！
22.对于魔方群，Y commutator：[F, R−1 ] = F · R−1 · F−1 · R
    Z commutator：[F, R] = F · R · F−1 · R−1
23.关于魔方群的只改变魔方本身有限块的位置的定理：如果 x、y 是魔方的基本移动，与共享边的面相关联，则
    1.[x， y]^2 正好置换 3 个边块，不改变任何角块;
    2.[x， y]^3 正好置换 2 个角块，不置换任何边块。
24.1. subgroup：子群
24.对于群G，commutator subgroup of G:是一个G的子群，里面的元素是所有的commutator [g,h]，这样的commutator由G中的任意两个元素g,h生成。
    具体定义是：{[g, h] | g, h belong to G}
    有趣的事实：当commutator subgroup足够大时，基本上和魔方群是相差无几的。也就是说，任意魔方状态基本都通过一组commutator可以达到。
25.对于群G，derived series：是一个序列的子群：... ⊂ (G‘)‘ ⊂ G’ ⊂ G
    以此前提，对于群G，可以定义solvable 可解群：derived series代表的序列中，有一个群是只有一个元素的，该元素是恒等变换。
26.对于群G，g、h是G中的元素，conjugate of g by h 共轭:是一个G中的元素，记为g^h, g^h = h−1 ∗ g ∗ h
27.对于群G，g1、g2是G中的元素, two elements g1,g2 are conjugate: 是一种关系，
    需要满足：如果存在一个元素 h ∈ G，使得 g2= g1^h =  h−1 ∗ g ∗ h
    判断是否共轭也有一个柯西定理
28.2.对于集合S，R是S的一个关系， equivalence relation：满足自反性+对称性+传递性。
28.1.对于集合S，R是集合S的一个等价关系，s是集合S的任意一个元素，the equivalence class of s in S：是集合S的一个子集，
    具体定义：[s] = {t ∈ S | s ∼ t} ， 也就是记为[s]
28.对于群G，在等价关系“conjugation”下的 等价类的集合 G∗：是一个由等价类组成的集合，元素是一个个等价类???, 记为G∗。
    以此前提，对于群G，可以定义一个多项式generating polynomial  of the order function on  G  ：
     是一个多项式，变量是t，p G (t) = ∑c∈G∗ t^order(c)
29.对于群G，g是G中的一个元素，the conjugacy class of g in G :是一个集合，里面的元素由任意h通过conjugate运算得到，
    因为conjugate这个关系是等价关系来的，等价关系可以理解成等价类，由于某种原因???可以把群G分成若干个类，所以每一个conjugate的计算结果可以代表一个等价类。
    具体定义为：记为 Cl(g) 或 ClG (g)，Cl(g) = ClG (g)  = {h−1 ∗ g ∗ h | h ∈ G}
30.对于群G，X是一个群G的子集，G acts on X on the right:G和X的一个关系，需要满足：(这个定义的实际例子我觉得是G的元素分别作用在边块X1和角块X2上，所以要研究这样的作用在子集上的映射)
    1.属于 G 的每个 g元素，对应产生一个函数φ：X → X
    2.群 G 的恒等式 1 定义了 X → X 上的恒等式函数。
    3. 如果 g、h 属于 G，则复合φgh：X → X满足：φgh(x) = φh(φg(x))
  同样类似可以定义G acts on X on the left，唯一不同之处是第3点：
    3.如果 g、h 属于 G，则复合φgh：X → X满足：φgh(x) = φg(φh(x))
  以此为前提，可以定义某个action is transitive：action φ的一个可选性质。
    需要满足：如果对于属于 X 的每对 x、y 都存在有一个 g ∈ G，该g对应的动作φ满足 y = φ（x），称该g对应的动作φ为transitive的。
31.对于群G，设满足G acts on X的关系,  the orbit of x∈X under G
    :是一个X的子集，其中元素这样生成的，对于某个特定的X中的元素x，
    任意取一个G中的元素g，g对应的action φ作用在x上得到的所有结果，这个结果组成的集合就是orbit。
    具体定义：G ∗ x = {φg(x) | g ∈ G} ， 记为G ∗ x
    对于魔方群G，X指的是魔方上的绝对位置，位置当作元素，这样的集合orbit其实可以分成两个集合V，E，两个块的绝对位置的集合
        这两个集合V，E仍然分别满足定义G ∗ x = {φg(x) | g ∈ G}，
        也就是仍然满足V，E中的元素经过φg映射后，仍然分别在V,E集合里面。
32.对于群G，集合X，设满足G acts on X的关系，x是X中的一个元素，stablizer：是一个G中元素的集合G2，G2里面的任意元素g，
    g需要满足条件是：φg作用在x后，结果仍然是x。
    具体定义：stabG (x) = Gx = {g ∈ G | φg (x) = x} ， 记为stabG (x) 或 Gx
33.对于群G，集合X这时取为G本身，即X=G，假设满足G acts on X的关系，G acts on X的关系中函数φ给出了固定的定义是 g ∗ x ∗ g−1
     ，centralizer of x in G：是一个G中元素的集合G2，首先我们知道stabG (x) = {g ∈ G | g ∗ x = x ∗ g}，这个集合
     stabG (x)就是我们的结果G2，记为CG(x)，CG(x)=stabG (x)。
34.对于魔方群G，g是G的元素，H集合={1,D,D^2,D^3} left coset of H:是一个作用左乘结果的集合，g左乘H中全体元素的结果，
    这些结果的集合就是left coset of H , 记为gH。
35.subset ： 子集合
36.对于群G，H是G的子群，g是G的元素， left coset of H in G: 是一个G的子集， 形式是这样的g*H,或写成gH，换句话说，就是
    选定g元素后，g左乘H中全体元素得到的结果，这些结果的集合就是 left coset of H in G。
    全体的 left coset of H in G集合（每个不同之处在于g的选取），再拼成的一个大集合，记为G/H。
    类似的，全体的 left coset of H in G集合（每个不同之处在于g的选取），再拼成的一个大集合，记为G\H。左右斜杠不同
37.对于群G，H是G的子群，拉格朗日定理：描述left coset of H in G集合的元素数量，直接可以用G的数量，H的数量计算出来。
38.对于群G，H是G的子群，C是一个G的子集a left coset of H in G, g是G中的元素
     coset representative of C：是群G中的一个元素g，g满足：C= g * H。 其实就是left coset of H in G定义中选取的某个g元素。
    全体 coset representatives，也可以称作全体coset representatives of G/H ：是一个G的子集，
        里面的元素比如有m个的话：x1,x2,...,xm , 这m个元素需要满足：
        G/H = {x1*H,x2*H,...,xm*H} , 还需要满足：x1*H , x2*H ,..., xm*H 这m个G的子集是互不相交的。
39.定理5.11.2: 全体coset representatives of G/H 可以构造出完整的群G。G = U(s∈S) s*H , 即一个并集，“每一个集合”是
    全体 coset representatives 某一项xk，xk右乘集合H得到的所有结果，这些所有结果的集合就是上面并集里的“每一个集合”。
40.对于群G1,群G2,映射f:G1→G2,*₁是群G1的运算，*₂是群G2的运算，f是  homomorphism 同态:映射f的一种可选性质，
    描述是G1和G2之间的一种关系，
    对于任意a,b∈ G1 , G1和G2需要满足：f(a *₁ b) = f(a) *₂ F(b) 。 注意：记号·和“并列写法”也可以代表* 。
41.对于群G1,群G2,映射f:G1→G2，f满足homomorphism， image of f:是群G2的一个子群 ,
    具体定义：f (G1 ) = {g ∈ G2 | g = f (x), for some x ∈ G1 }，换句话说，元素形式是g∈ G2,
    需要满足：能找到至少一个x ∈ G1 ，x通过映射f映射后是g。
    , 记为im(f) 。
42.对于群G1，群G2 , G1 embeds(or injects) into G2 单射：是G1和G2之间的一种关系，需要满足：能找到一个映射f:G1→ G2, 映射f是单射的。
    也就是相同结果推相同原像。
43.对于群G1,群G2,映射f:G1→G2，f满足homomorphism，  isomorphism 同构:f的一种可选性质，f需要满足：映射f是双射的。
    以此为前提，isomorphic:G1和G2的一种关系，满足f是isomorphism的， 记为G1≃G2。
    以此为前提，如果G1=G2，automorphism 自同构：f的一种可选性质，描述G1和G2的一种关系。
44.引理9.2.1:描述了G acts on X ↔ 存在同态的映射f， f满足：是一个这样类型的映射G→S×(这个集合指的是X中的元素的所有排列的集合，
    每一个排列可以用一个向量来表示)， 然后具体定义是将G中的任意元素g，映射到φg
    (这个φg是一个X→X类型的映射，作用到X里元素结果封闭在X里)
45. 对于群G，集合X，设满足G acts on X×X − ∆的关系，(X×X − ∆)整体是一个集合, ∆具体定义是∆ = {(x, x) | x ∈ X} 即diagonal对角的二维的集合，
    换句话说就是每一个分量都相同的二维的向量
    ，doubly transitive:
    G和 （二维X集合 - 对角集合）之间的一种关系，而且附加了可选性质transitive。
46.对于群G，集合X，设满足G acts on X的关系 ,  k-tuply transitive:是关系action（关系action，
    具体是指G和X需要满足的几个条件形成的一个总的命题）的一种可选性质。需要满足：
    对于向量A(x1,x2,...,xk) 和 向量B(y1,y2,...,yk) , A和B中的每一个分量都来自集合X，
    向量A都满足：A中每个分量都是互不相同的，换句话说就是xi≠xj
    向量B同样：B中每个分量都是互不相同的，换句话说就是yi≠yj
    A和B还有一点命题需要满足：对于每一个i,1<=i<=k,都存在一个群G中的元素g，由于满足假设“G acts on X”这个关系，每个g存在映射φg,
        而这个φg需要满足：yi = φg（xi），换句话说就是，可以将A中的每个分量映射到B中的对应位置的分量，
        比如A第1位x1映射到第一位y1,并且可以同时把x2映射到第一位y2,...,一直到 把xk映射到第一位yk。所以看起来条件非常苛刻。
47.1.对于集合Cn={0,1,...,n-1}，整数n>1,集合Cn满足群的定义， cyclic group of order n 循环群:是一个群 ,
    群的第一运算定义为“两元素相加，再模n的结果” 也记为Z/nZ。
47.4阶循环群，记为C4。对于魔方群G，R是魔方群G中的一个元素， 有一个引理： C4 ≃ H , 这里H是<R>,换句话说，H是由集合{R}生成的置换群
    （也就是说集合{R}生成的每一个元素都是一个置换，比如对于魔方群就是一个54项的向量，54项向量→54项向量的一个映射）。
48.对于群G1,群G2,映射f:G1→G2，f满足homomorphism，而且f满足isomorphism，且G1=G2，f具备性质automorphism，f的automorphism性质是  inner 内同构
    : automorphism的一种可选性质，对于群G1，g是群G1的元素，h是G1中的已选定的元素,
    automorphism需要满足：f映射满足:f是这种形式的：Ch(g) = h · g · h^−1 , g ∈ G.
    以此为前提，Aut(G)：是全体的automorphism，换句话说，是一个集合，集合里面元素是automorphism
        （通常用对象f来代表这样的automorphism性质，因为首先要有映射，才有自同构的性质的）。
    以此为前提，Inn(G)：是全体的automorphism，这些automorphism需要满足：具备inner性质 。具体定义：Inn(G):={f ∈ Aut(G) | f = ch , some h ∈ G}
        换句话说，就是首先是全体的automorphism， 后面的条件说的是，存在至少一个h，h是G中的元素,f需要满足：f等于Ch（换句话说，就是f能写成Ch的形式，也就是具备inner性质）。
    以此为前提，可以定义outer:automorphism的一种可选性质 , 不是inner的automorphism，就称作automorphism具备性质outer。
49.引理9.3.2，an inner automorphism must ‘preserve the cycle structure’ 内自同构“保持循环结构” ：对于内自同构的映射f,
    引理描述了一组不相交的循环（比如(1,2,4,3)这样是一个循环，是一个映射）的乘积A，经过f映射后，得到的结果仍然是不相交的循环的乘积B。
50.对于群G1,群G2,映射f:G1→G2，f满足homomorphism ,e₂是G2的单位元, the kernal of f 核:是群G1的一个子集，
    具体定义： kernal(f) = {g ∈ G1 | f(g) = e₂ } 换句话说，g需要满足：经过f映射后，结果是G2中的单位元。
51.对于群G1,群G2,映射f，f满足homomorphism，引理9.4.2:描述1.单射与kernal的互推关系，
    2.对于G1中任意元素x，对于kernal(f)中的任意元素g, 则=> , (x^-1·g·x)也是kernal(f)中的元素
52.对于群G，H是群G的子群， normal 正态or正定:子群H的一个可选性质，需要满足：g是G中任意的元素， (g^-1)·H·g=H
    （注意：这里 (g^-1)·H写法是left coset of H的意思，((g^-1)·H)·g同样类似的理解成right coset of ((g^-1)·H)）
    换句话说，就是对于任意g∈ G, 任意h∈ H , (g^-1)·H·g 集合 = H集合。
    换句话说，往元素的角度来看，就是任意g∈ G, 任意h∈ H， (g^-1)·h·g ∈ H
    ，称作H is a normal subgroup of G, 记为H◃G
53.trivial group: 只包含单位元e的群，通常称作平凡群。
54.对于群G1,群G2,映射f，f满足homomorphism， 引理9.4.3:描述了kernal(f) is a normal subgroup of G1。
55.sgn:是一个Sn到正负1集合的映射，Sn → {+1,-1},具体定义： Sn中元素s排列是even时，结果为1；s排列是odd时，结果为-1
56.An:是一个Sn的子集，具体定义就是ker(sgn)， An = ker(sgn) ⊂ Sn
57.9.4.2节内容与“不能用根式求解5次或更高次的多项式”有莫大关系，但是没有深入讲。
57.对于An，n满足n>=5，H是An的一个子群，满足H◃An, 引理9.4.1：H只能是这两个集合：H={1} or H=An。 换句话说，H不能是非平凡的。
58.对于排列群Sn,H是Sn的子群，H由某个集合I里面元素生成，集合I满足：I里面元素是的Sn中的全体的3循环的元素(换句话说，就是比如元素g^3=g,这样的全体g构成了I集合),
    命题9.4.1: 如果前面这些假设成立，则=>,sgn是Sn→{+1,-1}的映射，H=An 换句话说，H=An=ker(sgn) ⊂ Sn ,H集合就是An。
    （和“3循环”有莫大的联系，魔方群定义的重要关键定理。）
59.对于群G，群H，满足H◃G， quotient group of G by H: the coset space G/H with 二元运算定义为 aH·bH:=(ab)H,
    (aH)^-1 = a^-1H。换句话说，是一个自定义的空间A(也是一个集合)，A里面的元素是gH这样的集合，其中g是G的元素，对于任意两个A中的元素，
    比如aH,bH, 是两个集合来的，他们之间定义第一个运算·为 aH·bH:=(ab)H。
    可以证明这样的A集合，加上自定义的这个运算·，A是满足可选性质“A是一个群”的，此处没证明。
    A群的单位元就是trivial coset H, 也就是e为G的单位元，eH这个元素（实际上是一个集合）。
    A群记为 the quotient group of G by H 商群, 也可以记为"G mod H",也可以记为“factor group”
60.对于群G， abelianiation of G:是一个商群quotient group of G by G'商群, 记为Gab = G/G', 其中G' = [G,G]。
61.对于群G，proper subgroup：是一个G的子群A的一个可选性质，A需要满足：不是整个群，即不是G本身。
62.对于群G，a simple group:是群G的一个可选性质，群G需要满足：
    {任意群G的子群H，H满足H◃G 且 H不等于G本身 ，则=>, H等于{1},{1}恰巧可以称为trivial subgroup }
63.对于群G1,群G2,映射f:G1→G2，f满足homomorphism，定理9.5.1 First isomorphism theory 第一同构定理 :
    满足前面的假设条件的话，则=>,G1/ker(f) is isomorphic to(同构于) f(G1), 这里f(G1)指的是G1全体元素通过映射f后得到的结果元素的全体。
64.对于群G，群H，N都是群G的子群，N满足：N是normal正定的，定理9.5.2 Second isomorphism theory 第二同构定理 ：
    满足前面的假设条件的话，则=>,有两个结论：
    1. (H ∩ N)这个交集A满足：A is normal in H
    2. 存在一个isomorphism同构f，f满足：
        H/(H∩N) ≃ NH/N
        这里NH指的是一个集合B，B满足：B中的任意个元素，是这样生成的：由N中任意元素和H中任意元素通过G中的第一运算*，组合计算出来的。
        NH举例：
            假设我们有一个群 G，其中的元素由整数模 6 的剩余类表示。我们定义两个子群：
            H = {0, 2, 4}，包含模 6 余数为 0、2 和 4 的整数。
            N = {0, 3}，包含模 6 余数为 0 和 3 的整数。
            现在我们来找到 H⋅K。
            首先，我们按照群运算（加法）将 H 和 N 的元素进行组合：
            H + N = {0 + 0, 0 + 3, 2 + 0, 2 + 3, 4 + 0, 4 + 3} = {0, 3, 2, 5, 4, 1}
            所以知道HN = NH = {0, 3, 2, 5, 4, 1} = {0, 1, 2, 3, 4, 5}
65.对于群G，群N1，N2都是群G的子群，N1和N2满足：N1 ⊂ N2 ，且N1 is normal正定 ,且N2 is normal正定，定理9.5.3 Third isomorphism theory 第三同构定理 ：
    满足前面的假设条件的话，则=>,有两个结论：
    1. N2/N1 is normal in G/N1 . (那前提条件肯定满足： N2/N1 是 G/N1 的子群，这个为什么呢？)
    2.存在一个isomorphism同构f，f满足：
        (G/N1) / (N2/N1) ≃ G/N2  （感觉像一个除法的类似的东西）
66.对于群H，H1和H2是群H的子群, the direct product of H1 with H2:是一个群G，群G的元素是一个个的二项向量，记为G= H1 × H2，
    G需要满足：
    1.G的元素是一个个这样的二项向量(x,y), 换句话说，x是H1的元素，y时H2的元素。
    2.G的第一运算定义为：(x1,y1) · (x2,y2)= (x1·x2 , y1·y2) , 这里乘法符号“·”出现了3次，分别代表三个群的第一运算：G,H1,H2。
67.定理9.6.1 First Fundamental Theorem of Rubik’s Cube theory 魔方第一基本定理：魔方的一个状态是由以下性质来决定的：
    1.边块的排列
    2.角块的排列
    3.中心块的排列
    4.全体边块的翻转情况（相对于还原状态的时候）
    4.全体角块的翻转情况（相对于还原状态的时候）
68.9.9.3节中，
    H，the slice group ：是一个群，由〈MR , MF , MU 〉也就是由魔方群中的3个元素（操作），这3个元素
    是魔方中的3个中间层滑动 the middle slice move。
    X :是一个魔方面的集合，X里面的元素是魔方中的48个面，不包含6个中心面，所以是54-6=48
    G :魔方群(可推断出，为SX的一个子群？54反而是48的子群吗？)。
    V ：是一个魔方面的集合，V里面的元素是魔方中的角块的全体面。
    E ：是一个魔方面的集合，E里面的元素是魔方中的边块的全体面。
    C ：是一个魔方面的集合，C里面的元素是魔方中的中心块的全体面。
    F ：是一个群(可推断出，为SX的一个子群)，由魔方群G中的某些元素gi生成，这些元素gi满足:不会重新排列角块和边块的位置，
        但可能会改变角块或边块的角度。
    SX : 是一个symmetric对称群，是X集合上的对称群。
    SV : 是一个symmetric对称群(可推断出，为SX的一个子群)，是V集合上的对称群。
    SE : 是一个symmetric对称群(可推断出，为SX的一个子群)，是E集合上的对称群。
    GV = SV ∩ G
    GE = SE ∩ G
    FV = SV ∩ F
    FE = SE ∩ F
69.C3 4（这里表示C4的4上面有个3）：目前定义不太明确：1.C4的3次笛卡尔积，也就是说一个3项的向量。
70.


进度：P192/329
下一个里程碑218开始研究可解的魔方状态
224魔方第二基本定理已经可以开始做lean了
后面还有平方群的定理233-250
跳过14章太难了 --no
290有我们想要证明的52步算法，多种魔方解法284-
188出现了质疑，跳过了。



看完一二基本定理的证明后就看TW算法，书里面只有一页介绍，所以要看北师大老师的视频
然后再看这里项目的内容看看如何形式化，有哪些相关的
看看能否形式化出更多书里已看的定理，还有视频看到的算法
