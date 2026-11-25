/-
Written on the Wall II, conjecture 138 (Graffiti.pc, 2005-07-12).

18 阶树 T18 是一个反例。按定义 74 的标题，u 表示最大独立集的唯一性；
最大度顶点之间的距离在平方图中计算。

S0_unique_maximum 与 S0_card 给出唯一的 11 元最大独立集。
M_sq 与 square_dist18 给出平方图的两个最大度顶点 1、13 及距离 5。
T18_path_le 与 T18_path_attained 给出最长诱导路的确切顶点数 14。
connected_counterexample 合并连通性与猜想在 T18 上的否定：14 < (2 + 1) * 5。

验证环境：Lean 4.37.0-rc1，Mathlib c44d09c9afd6296ba2d4c0c3712b3592ac899078。
在对应的 Mathlib 工程中运行 lake env lean /path/to/Wowii138.lean。
-/
import Mathlib

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false

namespace Wowii138

/-! ## 一、猜想的表述（对任意有限简单图） -/

section Definitions

variable {V : Type} [Fintype V] [DecidableEq V]

/-- 取列表 `l` 的第 `i` 个元素（需要 `i < l.length` 的证明）。就是 `l[i]`，只是写法更稳妥。-/
abbrev nth {α : Type} (l : List α) (i : Nat) (h : i < l.length) : α := GetElem.getElem l i h

/-- 由 `i + 1 < j < l.length` 得到 `i < l.length`。-/
theorem lt_length_of_lt_length {α : Type} {l : List α} {i j : Nat} (hij : i + 1 < j)
    (hj : j < l.length) : i < l.length := by omega

/-- 平方图 `G²`：两个不同的顶点相邻，当且仅当它们在 `G` 中的距离是 1 或 2（原表定义 75）。 -/
@[reducible] def sq (G : SimpleGraph V) : SimpleGraph V where
  Adj a b := a ≠ b ∧ (G.Adj a b ∨ ∃ c, G.Adj a c ∧ G.Adj c b)
  symm := ⟨fun _ _ ⟨hne, h⟩ => ⟨hne.symm, by
    rcases h with h | ⟨c, h1, h2⟩
    · exact Or.inl (G.symm.symm _ _ h)
    · exact Or.inr ⟨c, G.symm.symm _ _ h2, G.symm.symm _ _ h1⟩⟩⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h rfl⟩

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- 邻接关系对称。 -/
theorem adj_symm {a b : V} (h : G.Adj a b) : G.Adj b a := G.symm.symm _ _ h

/-- 没有自环。 -/
theorem adj_irrefl (a : V) : ¬ G.Adj a a := G.loopless.irrefl a

instance : DecidableRel (sq G).Adj := fun _ _ => inferInstance

/-- 顶点 `v` 在 `G` 中的度数。 -/
def deg (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Nat :=
  (Finset.univ.filter fun w => G.Adj v w).card

/-- `M(G)`：`G` 中度数最大的顶点组成的集合（原表定义 34）。 -/
def M (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => ∀ w, deg G w ≤ deg G v

/-- 从 `a` 到 `b`、恰含 `n` 条边的游走：长度为 `n + 1` 的顶点序列，相邻两点在 `G` 中相邻，
第一个点是 `a`，最后一个点是 `b`。 -/
def Walk (G : SimpleGraph V) (a b : V) (n : Nat) : Prop :=
  ∃ l : List V, l.length = n + 1 ∧ l.IsChain G.Adj ∧ l.head? = some a ∧ l.getLast? = some b

/-- 两点间的距离：最短游走的边数（原表定义 19 中的 `dist_G`）。 -/
noncomputable def dist (G : SimpleGraph V) (a b : V) : Nat := sInf {n | Walk G a b n}

/-- `dist_min(M(G))`：`M(G)` 中两个不同顶点之间的最小距离（原表定义 19）。`|M(G)| ≤ 1` 时为 0。 -/
noncomputable def distMin (G : SimpleGraph V) [DecidableRel G.Adj] : Nat :=
  sInf {n | ∃ a ∈ M G, ∃ b ∈ M G, a ≠ b ∧ dist G a b = n}

/-- 独立集：集合中任意两个不同的顶点都不相邻。 -/
def IsIndependent (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ {a}, a ∈ S → ∀ {b}, b ∈ S → a ≠ b → ¬ G.Adj a b

instance (G : SimpleGraph V) (S : Finset V) [DecidableRel G.Adj] : Decidable (IsIndependent G S) := by
  unfold IsIndependent; infer_instance

/-- `G` 恰有一个最大独立集（原表定义 74 的标题；其正文漏写了 "maximum"）。 -/
def UniqueMaxIndependent (G : SimpleGraph V) : Prop :=
  ∃ S₀ : Finset V, IsIndependent G S₀ ∧
    ∀ S, IsIndependent G S → S.card ≤ S₀.card ∧ (S.card = S₀.card → S = S₀)

/-- `u(G)`：有唯一最大独立集时为 1，否则为 0。 -/
noncomputable def u (G : SimpleGraph V) : Nat :=
  open Classical in if UniqueMaxIndependent G then 1 else 0

/-- 诱导路，归纳定义。
`cons` 一条的含义：在诱导路 `w :: l` 前面接上 `v`，要求 `v` 与 `w` 相邻、`v` 与 `l` 中任何点都不相邻
（没有弦）、且 `v` 不在 `w :: l` 里（顶点不重复）。 -/
inductive IsInducedPath (G : SimpleGraph V) : List V → Prop
  | nil : IsInducedPath G []
  | single (v : V) : IsInducedPath G [v]
  | cons (v w : V) (l : List V) (hadj : G.Adj v w) (hchord : ∀ x ∈ l, ¬ G.Adj v x)
      (hfresh : v ∉ w :: l) (h : IsInducedPath G (w :: l)) : IsInducedPath G (v :: w :: l)

/-- 诱导路的教科书式表述：顶点不重复、相邻两点相邻、下标相差超过 1 的两点不相邻。 -/
def IsInducedPath' (G : SimpleGraph V) (l : List V) : Prop :=
  l.Nodup ∧ l.IsChain G.Adj ∧
    ∀ i j (hij : i + 1 < j) (hj : j < l.length),
      ¬ G.Adj (nth l i (lt_length_of_lt_length hij hj)) (nth l j hj)

/-- **Written on the Wall II 第 138 号猜想**：`path(G) ≥ (2 + u(G)) · dist_min(M(G²))`。
`path(G)` 是最长诱导路的顶点数（原表定义 35），所以不等式等价于存在一条至少这么多顶点的诱导路。 -/
def Conjecture138 (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ l : List V, IsInducedPath G l ∧ (2 + u G) * distMin (sq G) ≤ l.length

end Definitions

/-! ## 二、一般性引理 -/

section Lemmas

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- `a :: b :: t` 是链，当且仅当 `a` 与 `b` 相邻且 `b :: t` 是链。 -/
theorem isChain_cons_cons {R : V → V → Prop} {a b : V} {t : List V}
    (h : (a :: b :: t).IsChain R) : R a b ∧ (b :: t).IsChain R := by
  rcases List.isChain_cons_iff R a (b :: t) |>.mp h with hl | ⟨b', t', hab, ht, hl⟩
  · exact absurd hl (List.cons_ne_nil b t)
  · cases hl
    exact ⟨hab, ht⟩

theorem isChain_cons_cons' {R : V → V → Prop} {a b : V} {t : List V} (hab : R a b)
    (ht : (b :: t).IsChain R) : (a :: b :: t).IsChain R :=
  (List.isChain_cons_iff R a (b :: t)).mpr (Or.inr ⟨b, t, hab, ht, rfl⟩)

/-- 归纳定义推出教科书式表述。 -/
theorem IsInducedPath.toInducedPath' {l : List V} (h : IsInducedPath G l) : IsInducedPath' G l := by
  induction h with
  | nil =>
      refine ⟨by simp, by simp, ?_⟩
      intro i j _ hj
      exact absurd hj (Nat.not_lt_zero j)
  | single v =>
      refine ⟨by simp, by simp, ?_⟩
      intro i j hij hj
      have hj1 : j < 1 := hj
      omega
  | cons v w l hadj hchord hfresh h ih =>
    obtain ⟨hnd, hchain, hcd⟩ := ih
    refine ⟨List.nodup_cons.mpr ⟨hfresh, hnd⟩, ?_, ?_⟩
    · cases l with
      | nil => exact isChain_cons_cons' hadj (List.isChain_singleton w)
      | cons b t => exact isChain_cons_cons' hadj hchain
    · intro i j hij hj
      have hl : (v :: w :: l).length = l.length + 2 := by simp
      rw [hl] at hj
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
      have hl1 : (w :: l).length = l.length + 1 := by simp
      rcases Nat.eq_zero_or_pos i with hi0 | hpos
      · obtain rfl : i = 0 := by omega
        have hm : j' < l.length := by omega
        show ¬ G.Adj v (nth l j' hm)
        exact hchord _ (List.getElem_mem _)
      · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        have hm : j' + 1 < (w :: l).length := by omega
        show ¬ G.Adj (nth (w :: l) i' (by omega)) (nth (w :: l) (j' + 1) hm)
        exact hcd i' (j' + 1) (by omega) hm

/-- 教科书式表述推出归纳定义。 -/
theorem isInducedPath_of {l : List V} : IsInducedPath' G l → IsInducedPath G l := by
  induction l with
  | nil => exact fun _ => IsInducedPath.nil
  | cons v t iht =>
    intro h
    obtain ⟨hnd, hchain, hcd⟩ := h
    rcases t with _ | ⟨w, l⟩
    · exact IsInducedPath.single v
    · obtain ⟨hvw, hchain_tail⟩ := isChain_cons_cons hchain
      obtain ⟨hfresh, hnd_tail⟩ := List.nodup_cons.mp hnd
      refine IsInducedPath.cons v w l hvw ?_ hfresh (iht ⟨hnd_tail, hchain_tail, ?_⟩)
      · intro x hx
        obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hx
        have hl2 : m + 2 < (v :: w :: l).length := by simp only [List.length_cons]; omega
        have h01 : 0 + 1 < m + 2 := by omega
        have hi0 : 0 < (v :: w :: l).length := by simp only [List.length_cons]; omega
        show ¬ G.Adj (nth (v :: w :: l) 0 hi0) (nth (v :: w :: l) (m + 2) hl2)
        exact hcd 0 (m + 2) h01 hl2
      · intro i j hij hj
        have hl : (w :: l).length = l.length + 1 := by simp
        rw [hl] at hj
        have hi1 : i + 1 < (v :: w :: l).length := by simp only [List.length_cons]; omega
        have hj1 : j + 1 < (v :: w :: l).length := by simp only [List.length_cons]; omega
        show ¬ G.Adj (nth (v :: w :: l) (i + 1) hi1) (nth (v :: w :: l) (j + 1) hj1)
        exact hcd (i + 1) (j + 1) (by omega) hj1

/-- 归纳定义与教科书式表述等价。 -/
theorem isInducedPath_iff (l : List V) : IsInducedPath G l ↔ IsInducedPath' G l :=
  ⟨IsInducedPath.toInducedPath', isInducedPath_of⟩

/-- 诱导路的前缀仍是诱导路。 -/
theorem IsInducedPath.take {l : List V} (h : IsInducedPath G l) (n : Nat) :
    IsInducedPath G (l.take n) := by
  induction h generalizing n with
  | nil => simp only [List.take_nil]; exact IsInducedPath.nil
  | single v =>
      cases n with
      | zero => simp only [List.take_zero]; exact IsInducedPath.nil
      | succ n => simp only [List.take_succ_cons, List.take_nil]; exact IsInducedPath.single v
  | cons v w l hadj hchord hfresh h ih =>
      cases n with
      | zero => simp only [List.take_zero]; exact IsInducedPath.nil
      | succ n =>
          cases n with
          | zero =>
              simp only [List.take_succ_cons, List.take_zero]; exact IsInducedPath.single v
          | succ n' =>
              have hm : ∀ x, x ∈ l.take n' → x ∈ l := fun _ hx => List.take_subset n' l hx
              have hsub : ∀ x, x ∈ w :: l.take n' → x ∈ w :: l := by
                intro x hx
                rcases List.mem_cons.mp hx with rfl | hx'
                · exact List.Mem.head _
                · exact List.mem_cons.mpr (Or.inr (hm x hx'))
              simp only [List.take_succ_cons]
              refine IsInducedPath.cons v w (l.take n') hadj ?_ ?_ (ih (n' + 1))
              · intro x hx
                exact hchord x (hm x hx)
              · intro hx
                exact hfresh (hsub _ hx)

/-- `IsChain` 的序列中下标相邻的两点确实相邻。 -/
theorem isChain_getElem {R : V → V → Prop} {l : List V} (h : l.IsChain R) :
    ∀ k (hk : k + 1 < l.length), R (nth l k (by omega)) (nth l (k + 1) hk) := by
  intro k
  induction k generalizing l with
  | zero =>
      intro hk
      cases l with
      | nil => simp at hk
      | cons a t =>
          cases t with
          | nil => simp at hk
          | cons b t' =>
              have hk1 : 1 < (a :: b :: t').length := hk
              have hk0 : 0 < (a :: b :: t').length := by simp only [List.length_cons]; omega
              show R (nth (a :: b :: t') 0 hk0) (nth (a :: b :: t') 1 hk1)
              exact (isChain_cons_cons h).1
  | succ k ih =>
      intro hk
      cases l with
      | nil => simp at hk
      | cons a t =>
          have h1 : k + 1 < t.length := by simp only [List.length_cons] at hk; omega
          have hk1 : k + 2 < (a :: t).length := hk
          have hk0 : k + 1 < (a :: t).length := by omega
          show R (nth (a :: t) (k + 1) hk0) (nth (a :: t) (k + 2) hk1)
          exact ih (List.IsChain.tail h) h1

/-- `S` 诱导的子图中 `v` 的度数。 -/
def degIn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) : Nat :=
  (S.filter fun w => G.Adj v w).card

/-- `S` 中的每个顶点在 `S` 诱导的子图里度数都是 1 或 2。诱导路上的顶点都满足这一条。 -/
def PathLike (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Prop :=
  ∀ v ∈ S, 1 ≤ degIn G S v ∧ degIn G S v ≤ 2

instance (G : SimpleGraph V) (S : Finset V) [DecidableRel G.Adj] : Decidable (PathLike G S) := by
  unfold PathLike; infer_instance

/-- 集合非空则元素个数至少为 1。 -/
theorem one_le_card_of_mem {S : Finset V} {w : V} (h : w ∈ S) : 1 ≤ S.card :=
  Finset.card_pos.mpr ⟨w, h⟩

/-- 诱导路上每个顶点在诱导子图中的度数是 1（端点）或 2（内部点）。 -/
theorem IsInducedPath'.pathLike {l : List V} (h : IsInducedPath' G l) (hl2 : 2 ≤ l.length) :
    PathLike G l.toFinset := by
  obtain ⟨hnd, hchain, hcd⟩ := h
  have hstep := isChain_getElem hchain
  intro v hv
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hv)
  constructor
  · rcases Nat.eq_zero_or_pos i with hi0 | hpos
    · obtain rfl : i = 0 := by omega
      have h1 : 1 < l.length := by omega
      exact one_le_card_of_mem
        (S := l.toFinset.filter fun w => G.Adj (nth l 0 hi) w) (w := nth l 1 h1)
        (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (List.getElem_mem _), hstep 0 h1⟩)
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hj : j < l.length := by omega
      exact one_le_card_of_mem
        (S := l.toFinset.filter fun w => G.Adj (nth l (j + 1) hi) w) (w := nth l j hj)
        (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (List.getElem_mem _),
          adj_symm (hstep j (by omega))⟩)
  · show degIn G l.toFinset (nth l i hi) ≤ 2
    rcases Nat.eq_zero_or_pos i with hi0 | hpos
    · obtain rfl : i = 0 := by omega
      have h1 : 1 < l.length := by omega
      have hsub : l.toFinset.filter (fun w => G.Adj (nth l 0 hi) w) ⊆ {nth l 1 h1} := by
        intro x hx
        simp only [Finset.mem_filter] at hx
        obtain ⟨hx1, hadj⟩ := hx
        obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hx1)
        simp only [Finset.mem_singleton]
        have hm1 : m ≠ 0 := by
          intro e; subst e; exact adj_irrefl _ hadj
        have hm2 : ¬ (0 + 1 < m) := fun hc => hcd 0 m hc hm hadj
        obtain rfl : m = 1 := by omega
        rfl
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_singleton] at hcard
      show (l.toFinset.filter fun w => G.Adj (nth l 0 hi) w).card ≤ 2
      omega
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hj1 : j + 1 < l.length := hi
      -- 与 l[j + 1] 相邻的下标只能是 j 或 j + 2
      have hnb : ∀ m (hm : m < l.length), G.Adj (nth l (j + 1) hj1) (nth l m hm) →
          m = j ∨ m = j + 2 := by
        intro m hm hadj
        have h1 : ¬ (j + 1 + 1 < m) := fun hc => hcd (j + 1) m hc hm hadj
        have h2 : ¬ (m + 1 < j + 1) := fun hc => hcd m (j + 1) hc hj1 (adj_symm hadj)
        have h3 : m ≠ j + 1 := by
          intro e; subst e; exact adj_irrefl _ hadj
        omega
      have hj : j < l.length := by omega
      by_cases h2 : j + 2 < l.length
      · have hsub : l.toFinset.filter (fun w => G.Adj (nth l (j + 1) hj1) w) ⊆
            {nth l j hj, nth l (j + 2) h2} := by
          intro x hx
          simp only [Finset.mem_filter] at hx
          obtain ⟨hx1, hadj⟩ := hx
          obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hx1)
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rcases hnb m hm hadj with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
        have hcard := Finset.card_le_card hsub
        have hle2 : ({nth l j hj, nth l (j + 2) h2} : Finset V).card ≤ 2 := by
          have hle := Finset.card_insert_le (nth l j hj) ({nth l (j + 2) h2} : Finset V)
          rw [Finset.card_singleton] at hle
          exact hle
        show (l.toFinset.filter fun w => G.Adj (nth l (j + 1) hj1) w).card ≤ 2
        omega
      · have hsub : l.toFinset.filter (fun w => G.Adj (nth l (j + 1) hj1) w) ⊆ {nth l j hj} := by
          intro x hx
          simp only [Finset.mem_filter] at hx
          obtain ⟨hx1, hadj⟩ := hx
          obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hx1)
          simp only [Finset.mem_singleton]
          rcases hnb m hm hadj with rfl | rfl
          · rfl
          · exact absurd hm (by omega)
        have hcard := Finset.card_le_card hsub
        rw [Finset.card_singleton] at hcard
        show (l.toFinset.filter fun w => G.Adj (nth l (j + 1) hj1) w).card ≤ 2
        omega

/-- 沿着一条链，`pot` 每走一步至多增加 1。 -/
theorem pot_isChain (pot : V → Nat) (hlip : ∀ a b : V, G.Adj a b → pot b ≤ pot a + 1) :
    ∀ l : List V, l.IsChain G.Adj → ∀ x y, l.head? = some x → l.getLast? = some y →
      pot y ≤ pot x + (l.length - 1) := by
  intro l
  induction l with
  | nil => intro _ x y h; simp at h
  | cons a t iht =>
      intro hchain x y hhead hlast
      cases t with
      | nil =>
          have h1 : some a = some x := hhead
          have h2 : some a = some y := hlast
          obtain ⟨rfl, rfl⟩ : a = x ∧ a = y := ⟨Option.some.inj h1, Option.some.inj h2⟩
          omega
      | cons b t' =>
          obtain ⟨h1, h2⟩ := isChain_cons_cons hchain
          have hlast' : (b :: t').getLast? = some y := hlast
          have hpot := iht h2 b y rfl hlast'
          have hstep := hlip a b h1
          have hx : some a = some x := hhead
          obtain rfl : a = x := Option.some.inj hx
          have hl1 : (b :: t').length = t'.length + 1 := by simp
          have hl2 : (a :: b :: t').length = t'.length + 2 := by simp
          rw [hl2]
          rw [hl1] at hpot
          omega

/-- 游走给出距离的上界。 -/
theorem dist_le_of_walk {n : Nat} (hw : Walk G a b n) : dist G a b ≤ n :=
  Nat.sInf_le (s := {n | Walk G a b n}) hw

/-- 游走反过来仍是游走。 -/
theorem Walk.reverse (hw : Walk G a b n) : Walk G b a n := by
  obtain ⟨l, hlen, hchain, hhead, hlast⟩ := hw
  refine ⟨l.reverse, by simp [hlen], ?_, ?_, ?_⟩
  · exact (List.isChain_reverse.mpr hchain).imp fun _ _ hc => adj_symm hc
  · rw [List.head?_reverse]; exact hlast
  · rw [List.getLast?_reverse]; exact hhead

/-- 距离对称。 -/
theorem dist_comm (a b : V) : dist G a b = dist G b a := by
  unfold dist
  apply congrArg sInf
  ext n
  exact ⟨Walk.reverse, Walk.reverse⟩

/-- 距离由某个游走达到。 -/
theorem walk_of_dist {n : Nat} (h : Walk G a b n) : Walk G a b (dist G a b) :=
  Nat.sInf_mem (s := {n | Walk G a b n}) ⟨n, h⟩

/-- 自然数单点集合的下确界。 -/
theorem sInf_singleton_nat (n : Nat) : sInf ({n} : Set Nat) = n :=
  Set.mem_singleton_iff.mp (Nat.sInf_mem (s := {n}) (Set.singleton_nonempty n))

/-- 独立集的子集仍是独立集。 -/
theorem IsIndependent.subset {S T : Finset V} (hS : IsIndependent G S) (h : T ⊆ S) :
    IsIndependent G T := by
  intro a ha b hb hne
  exact hS (h ha) (h hb) hne

/-- 链上任意两点沿着邻接关系互相可达。 -/
theorem reflTransGen_of_isChain {R : V → V → Prop} (hsym : ∀ x y, R x y → R y x) :
    ∀ l : List V, l.IsChain R → ∀ x ∈ l, ∀ y ∈ l,
      Relation.ReflTransGen R x y ∧ Relation.ReflTransGen R y x := by
  intro l
  induction l with
  | nil => intro _ x hx; simp at hx
  | cons a t ih =>
    intro h x hx y hy
    have key : ∀ z ∈ a :: t, Relation.ReflTransGen R a z ∧ Relation.ReflTransGen R z a := by
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
      · cases t with
        | nil => simp at hz
        | cons b t' =>
            obtain ⟨hab, ht⟩ := isChain_cons_cons h
            rcases List.mem_cons.mp hz with hzb | hz'
            · subst hzb
              exact ⟨Relation.ReflTransGen.head hab Relation.ReflTransGen.refl,
                Relation.ReflTransGen.head (hsym _ _ hab) Relation.ReflTransGen.refl⟩
            · have hz'' : z ∈ b :: t' := List.mem_cons.mpr (Or.inr hz')
              obtain ⟨hz1, hz2⟩ := ih ht b (by simp) z hz''
              exact ⟨Relation.ReflTransGen.head hab hz1,
                Relation.ReflTransGen.tail hz2 (hsym _ _ hab)⟩
    by_cases hxa : x = a
    · subst hxa
      exact key y hy
    · have hx' : x ∈ t := (List.mem_cons.mp hx).resolve_left hxa
      obtain ⟨hx1, hx2⟩ := key x (List.mem_cons.mpr (Or.inr hx'))
      obtain ⟨hy1, hy2⟩ := key y hy
      exact ⟨hx2.trans hy1, hy2.trans hx1⟩

/-- 若关系 `r` 的每一步都不改变 `f` 的取值，则可达的两点取值相同。 -/
theorem eq_of_reflTransGen (f : V → Bool) {r : V → V → Prop} (h : ∀ x y, r x y → f x = f y)
    {u v : V} (hr : Relation.ReflTransGen r u v) : f u = f v := by
  induction hr with
  | refl => rfl
  | tail _ hc ih => rw [ih]; exact h _ _ hc

/-- 如果有函数 `f` 在 `H` 的每条边上取值相同，而 `f u = true`、`f v = false`，
那么 `u`、`v` 在 `H` 中互相不可达。 -/
theorem not_reachable_of_cut (H : SimpleGraph V) (f : V → Bool) {u v : V} (hu : f u = true)
    (hv : f v = false) (h : ∀ x y, H.Adj x y → f x = f y) : ¬ H.Reachable u v := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  intro hr
  have key : f u = f v := eq_of_reflTransGen f h hr
  rw [key] at hu
  rw [hv] at hu
  exact Bool.noConfusion hu

end Lemmas

/-! ## 三、18 个顶点的反例 `T18` -/

section T18

open Fin

/-- 顶点标号 0…17。`0` 接叶子 2、3、4 和顶点 1；`1-5-6-⋯-13` 是一条 9 条边的路；
`13` 接叶子 15 和顶点 14；`14` 接叶子 16、17。 -/
@[reducible] def adj18 (a b : Fin 18) : Prop :=
  let x := a.val
  let y := b.val
  (x = 0 ∧ (y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4))
    ∨ (y = 0 ∧ (x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4))
    ∨ (x = 1 ∧ y = 5) ∨ (x = 5 ∧ y = 1)
    ∨ (x = 13 ∧ (y = 14 ∨ y = 15)) ∨ ((x = 14 ∨ x = 15) ∧ y = 13)
    ∨ (x = 14 ∧ (y = 16 ∨ y = 17)) ∨ ((x = 16 ∨ x = 17) ∧ y = 14)
    ∨ ((5 ≤ x ∧ x ≤ 12) ∧ x + 1 = y)
    ∨ ((5 ≤ y ∧ y ≤ 12) ∧ y + 1 = x)

instance : DecidableRel (adj18 : Fin 18 → Fin 18 → Prop) := fun a b => by
  unfold adj18
  infer_instance

/-- 反例图。 -/
def T18 : SimpleGraph (Fin 18) where
  Adj a b := adj18 a b
  symm := ⟨by
    intro a b h
    revert h
    revert b
    revert a
    decide⟩
  loopless := ⟨by
    intro a h
    revert h
    revert a
    decide⟩

instance : DecidableRel T18.Adj := fun a b => (show Decidable (adj18 a b) from inferInstance)

/-- 与文稿一致的边表，用来核对邻接关系没有写错。 -/
def edges18 : List (Fin 18 × Fin 18) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (5, 6), (6, 7), (7, 8), (8, 9), (9, 10), (10, 11),
    (11, 12), (12, 13), (13, 14), (13, 15), (14, 16), (14, 17)]

/-- 边表有 17 条边，且每条列出的边在 `T18` 中确实相邻。 -/
theorem T18_edges_ok : edges18.length = 17 ∧ edges18.all (fun e => decide (T18.Adj e.1 e.2)) = true := by
  refine ⟨by decide, by decide⟩

/-- 一条经过全部 18 个顶点的链：4-0-3-0-2-0-1-5-⋯-13-15-13-14-17-14-16。 -/
def walkAll : List (Fin 18) :=
  [4, 0, 3, 0, 2, 0, 1, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 13, 14, 17, 14, 16]

theorem walkAll_isChain : walkAll.IsChain T18.Adj := by decide

theorem walkAll_mem : ∀ v : Fin 18, v ∈ walkAll := by decide

/-- 17 条边，以及每条边的一个割集：删掉这条边后，割集包含 `u`、不含 `v`，且没有边跨越它。 -/
def cutEdge : Fin 17 → Fin 18 × Fin 18 :=
  ![(2, 0),
    (3, 0),
    (4, 0),
    (0, 1),
    (1, 5),
    (5, 6),
    (6, 7),
    (7, 8),
    (8, 9),
    (9, 10),
    (10, 11),
    (11, 12),
    (12, 13),
    (15, 13),
    (13, 14),
    (16, 14),
    (17, 14)]

def cutSet : Fin 17 → Finset (Fin 18) :=
  ![{2},
    {3},
    {4},
    {0, 2, 3, 4},
    {0, 1, 2, 3, 4},
    {0, 1, 2, 3, 4, 5},
    {0, 1, 2, 3, 4, 5, 6},
    {0, 1, 2, 3, 4, 5, 6, 7},
    {0, 1, 2, 3, 4, 5, 6, 7, 8},
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9},
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10},
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11},
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12},
    {15},
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15},
    {16},
    {17}]

/-- 每个割集确实把它两侧分开。 -/
theorem cuts_ok : ∀ i : Fin 17,
    decide ((cutEdge i).1 ∈ cutSet i) = true ∧ decide ((cutEdge i).2 ∈ cutSet i) = false ∧
      ∀ x y : Fin 18, (T18.deleteEdges {Sym2.mk (cutEdge i).1 (cutEdge i).2}).Adj x y →
        decide (x ∈ cutSet i) = decide (y ∈ cutSet i) := by
  decide

/-- `T18` 的每条边都在上面的表里（可能方向相反）。 -/
theorem cuts_cover : ∀ u : Fin 18, ∀ v : Fin 18, T18.Adj u v →
    ∃ i : Fin 17, ((cutEdge i).1 = u ∧ (cutEdge i).2 = v) ∨
      ((cutEdge i).1 = v ∧ (cutEdge i).2 = u) := by
  decide

/-- `T18` 是树：连通（有一条经过全部顶点的链），并且无圈（每条边都是桥）。 -/
theorem T18_isTree : T18.IsTree := by
  refine SimpleGraph.IsTree.mk (SimpleGraph.Connected.mk ?_) ?_
  · intro v w
    exact (SimpleGraph.reachable_iff_reflTransGen v w).mpr
      (reflTransGen_of_isChain (fun x y h => adj_symm (G := T18) h) walkAll walkAll_isChain
        v (walkAll_mem v) w (walkAll_mem w)).1
  · refine SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mpr (by
      intro a b hab
      obtain ⟨i, hor⟩ := cuts_cover a b hab
      obtain ⟨h1, h2, hcross⟩ := cuts_ok i
      rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (SimpleGraph.isBridge_iff (G := T18) (u := (cutEdge i).1) (v := (cutEdge i).2)).mpr
          (not_reachable_of_cut _ (fun x => decide (x ∈ cutSet i)) h1 h2
            (fun x y hxy => hcross x y hxy))
      · have hbr : T18.IsBridge (Sym2.mk (cutEdge i).1 (cutEdge i).2) :=
          (SimpleGraph.isBridge_iff (G := T18) (u := (cutEdge i).1) (v := (cutEdge i).2)).mpr
            (not_reachable_of_cut _ (fun x => decide (x ∈ cutSet i)) h1 h2
              (fun x y hxy => hcross x y hxy))
        simpa only [Sym2.eq_swap] using hbr)

/-! ## 四、唯一最大独立集、平方图距离与诱导路 -/

/-- 反例的唯一最大独立集。 -/
def S0 : Finset (Fin 18) := {1, 2, 3, 4, 6, 8, 10, 12, 15, 16, 17}

theorem S0_card : S0.card = 11 := by decide

private def mark (S : Finset (Fin 18)) (v : Fin 18) : Nat := if v ∈ S then 1 else 0

/-- 七条不相交的边各至多贡献一点；取等时，四个未匹配点和每条边上的选择都被迫确定。 -/
theorem S0_unique_maximum : IsIndependent T18 S0 ∧
    ∀ S, IsIndependent T18 S → S.card ≤ S0.card ∧ (S.card = S0.card → S = S0) := by
  refine ⟨by decide, ?_⟩
  intro S hS
  have total : S.card = ∑ v, mark S v := Finset.card_eq_sum_ite (Finset.subset_univ S)
  simp only [Fin.sum_univ_ofNat] at total
  have edge (a b : Fin 18) (h : T18.Adj a b) : mark S a + mark S b ≤ 1 := by
    have hn := adj_irrefl (G := T18)
    by_cases ha : a ∈ S
    · have hb : b ∉ S := fun hb => hS ha hb (fun e => hn b (e ▸ h)) h
      simp [mark, ha, hb]
    · simp [mark, ha]
      split <;> decide
  have unit (a : Fin 18) : mark S a ≤ 1 := by unfold mark; split <;> decide
  have m0 := edge 0 2 (by decide)
  have m1 := edge 1 5 (by decide)
  have m2 := edge 6 7 (by decide)
  have m3 := edge 8 9 (by decide)
  have m4 := edge 10 11 (by decide)
  have m5 := edge 12 13 (by decide)
  have m6 := edge 14 16 (by decide)
  have u3 := unit 3
  have u4 := unit 4
  have u15 := unit 15
  have u17 := unit 17
  rw [S0_card]
  constructor
  · omega
  · intro heq
    have tight : mark S 0 + mark S 2 = 1 ∧ mark S 1 + mark S 5 = 1 ∧
        mark S 6 + mark S 7 = 1 ∧ mark S 8 + mark S 9 = 1 ∧
        mark S 10 + mark S 11 = 1 ∧ mark S 12 + mark S 13 = 1 ∧
        mark S 14 + mark S 16 = 1 ∧ mark S 3 = 1 ∧ mark S 4 = 1 ∧
        mark S 15 = 1 ∧ mark S 17 = 1 := by
      repeat' constructor <;> omega
    obtain ⟨t0, t1, t2, t3, t4, t5, t6, l3, l4, l15, l17⟩ := tight
    have e03 := edge 0 3 (by decide)
    have e13 := edge 13 15 (by decide)
    have e14 := edge 14 17 (by decide)
    have e11 := edge 11 12 (by decide)
    have e9 := edge 9 10 (by decide)
    have e7 := edge 7 8 (by decide)
    have e5 := edge 5 6 (by decide)
    apply Eq.symm
    apply Finset.eq_of_subset_of_card_le _ (by rw [heq, S0_card])
    intro v hv
    have hmark : mark S v = 1 := by
      simp only [S0, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    simpa [mark] using hmark

theorem T18_unique : UniqueMaxIndependent T18 := ⟨S0, S0_unique_maximum⟩

theorem u18 : u T18 = 1 := by simp [u, T18_unique]

/-- 平方图的逐点度数与最大度顶点。 -/
private def squareDegrees : Fin 18 → Nat := ![5,6,4,4,4,4,4,4,4,4,4,4,5,6,5,3,3,3]

theorem square_degree18 : ∀ v : Fin 18, deg (sq T18) v = squareDegrees v := by decide

theorem M_sq : M (sq T18) = {1, 13} := by
  ext v
  simp only [M, Finset.mem_filter, Finset.mem_univ, true_and, square_degree18]
  revert v
  decide

/-- 沿平方图的每条边，该函数至多增加一；它在 1 和 13 上的值相差五。 -/
private def pot18 : Fin 18 → Nat := ![1,0,1,1,1,1,1,2,2,3,3,4,4,5,5,5,6,6]

theorem square_dist18 : dist (sq T18) 1 13 = 5 := by
  have hw : Walk (sq T18) 1 13 5 := ⟨[1,6,8,10,12,13], rfl, by decide, rfl, rfl⟩
  apply Nat.le_antisymm (dist_le_of_walk hw)
  obtain ⟨l, hlen, hc, hh, ht⟩ := walk_of_dist hw
  have lip : ∀ a b, (sq T18).Adj a b → pot18 b ≤ pot18 a + 1 := by decide
  have bound := pot_isChain pot18 lip l hc 1 13 hh ht
  change 5 ≤ 0 + (l.length - 1) at bound
  omega

theorem distMin18 : distMin (sq T18) = 5 := by
  unfold distMin
  rw [M_sq]
  apply Eq.trans _ (sInf_singleton_nat 5)
  apply congrArg sInf
  ext n
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨a, ha, b, hb, hn, hd⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hn rfl).elim
    · exact hd.symm.trans square_dist18
    · exact hd.symm.trans ((dist_comm _ _).trans square_dist18)
    · exact (hn rfl).elim
  · rintro rfl
    exact ⟨1, Or.inl rfl, 13, Or.inr rfl, by decide, square_dist18⟩

/-- 去掉六个叶子后的全部十二个顶点。 -/
private def innerSites : Finset (Fin 18) := {0,1,5,6,7,8,9,10,11,12,13,14}

private theorem middle_site : ∀ a b c : Fin 18,
    T18.Adj a b → T18.Adj b c → a ≠ c → b ∈ innerSites := by decide

/-- 去掉两个端点后，简单路上每个顶点都与前后两个不同的点相邻。 -/
private theorem interior_subset (a b : Fin 18) (t : List (Fin 18))
    (hn : (a :: b :: t).Nodup) (hc : (a :: b :: t).IsChain T18.Adj) :
    (b :: t).dropLast.toFinset ⊆ innerSites := by
  induction t generalizing a b with
  | nil => simp
  | cons c t ih =>
    obtain ⟨hab, htail⟩ := isChain_cons_cons hc
    have hbc := (isChain_cons_cons htail).1
    have hac : a ≠ c := fun e => (List.nodup_cons.mp hn).1 (by simp [e])
    intro v hv
    change v ∈ (b :: (c :: t).dropLast).toFinset at hv
    rcases List.mem_cons.mp (List.mem_toFinset.mp hv) with rfl | hv
    · exact middle_site a _ c hab hbc hac
    · exact ih b c (List.nodup_cons.mp hn).2 htail (List.mem_toFinset.mpr hv)

theorem T18_path_le (l : List (Fin 18)) (h : IsInducedPath T18 l) : l.length ≤ 14 := by
  obtain ⟨hn, hc, _⟩ := h.toInducedPath'
  match l with
  | [] | [_] => simp
  | a :: b :: t =>
    have bound := Finset.card_le_card (interior_subset a b t hn hc)
    have hnd := (List.nodup_cons.mp hn).2
    have hd : (b :: t).dropLast.Nodup := hnd.sublist (List.dropLast_sublist _)
    rw [List.toFinset_card_of_nodup hd, List.length_dropLast] at bound
    have hcard : innerSites.card = 12 := by decide
    simp only [hcard, List.length_cons] at bound ⊢
    omega

/-- 从叶子 2 到叶子 16 的诱导路达到上界。 -/
theorem T18_path_attained : ∃ l, IsInducedPath T18 l ∧ l.length = 14 := by
  let l : List (Fin 18) := [2,0,1,5,6,7,8,9,10,11,12,13,14,16]
  refine ⟨l, ?_, rfl⟩
  apply isInducedPath_of
  -- 无弦性只需在这条路的十四个下标上检查。
  refine ⟨by decide, by decide, ?_⟩
  have check : ∀ i j : Fin 14, i.val + 1 < j.val → ¬ T18.Adj l[i.val] l[j.val] := by decide
  intro i j hij hj
  exact check ⟨i, by change j < 14 at hj; omega⟩ ⟨j, hj⟩ hij

theorem conjecture138_false : ¬ Conjecture138 T18 := by
  rintro ⟨l, hp, hlen⟩
  rw [u18, distMin18] at hlen
  have := T18_path_le l hp
  omega

/-- 在有限简单连通图的范围内给出反例。 -/
theorem connected_counterexample : T18.Connected ∧ ¬ Conjecture138 T18 :=
  ⟨T18_isTree.connected, conjecture138_false⟩

end T18
end Wowii138

#print axioms Wowii138.conjecture138_false
#print axioms Wowii138.connected_counterexample
#print axioms Wowii138.T18_path_attained
