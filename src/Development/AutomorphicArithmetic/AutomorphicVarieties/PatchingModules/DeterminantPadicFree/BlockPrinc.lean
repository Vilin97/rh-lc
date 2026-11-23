module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.CornerCoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.DTw
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Infres
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.RelMove
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Shapiro
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.DTwAlt

section

@[expose] public section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.eigen :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (κ la : G → Matrix (Fin n) (Fin n) F) (Y : Matrix (Fin n) (Fin n) F), TwCoc (fun _ => 1) D.r Set.univ κ → TwCoc D.χF D.r Set.univ la → (∀ g ∈ D.G', κ g + la g = dTw (fun _ => 1) D.r Y g) → (∃ Y₁, ∀ g ∈ D.G', κ g = dTw (fun _ => 1) D.r Y₁ g) ∧ ∃ Y₂, ∀ g ∈ D.G', la g = dTw (fun _ => 1) D.r Y₂ g := by
  intro F G _ _ n D κ la Y hκ hla hY
  set c : F := D.χF D.g₀ with hc
  have hc1 : c - 1 ≠ 0 := by
    intro h
    apply D.χ_ne
    ext
    exact sub_eq_zero.mp h
  set Z : Matrix (Fin n) (Fin n) F := D.r D.g₀ * Y * D.r D.g₀⁻¹ with hZ
  set Y₁ : Matrix (Fin n) (Fin n) F := (c - 1)⁻¹ • (c • Z - c • κ D.g₀ - la D.g₀ - Y) with hY₁
  have key : ∀ g ∈ D.G', κ g = dTw (fun _ => 1) D.r Y₁ g := by
    intro g hg
    have hg' : D.g₀⁻¹ * g * D.g₀ ∈ D.G' := by
      have := D.G'.mul_mem (D.comm D.g₀⁻¹ g) hg
      simpa using this
    set g' := D.g₀⁻¹ * g * D.g₀ with hgg
    have e : g * D.g₀ = D.g₀ * g' := by rw [hgg]; group
    have e' : g'⁻¹ * D.g₀⁻¹ = D.g₀⁻¹ * g⁻¹ := by rw [hgg]; group
    have h1 := hκ g trivial D.g₀ trivial
    have h2 := hla g trivial D.g₀ trivial
    rw [e, hκ D.g₀ trivial g' trivial] at h1
    rw [e, hla D.g₀ trivial g' trivial] at h2
    have hχ : D.χF g = 1 := by simp [DetFr.χF, D.χ_triv g hg]
    rw [hχ, ← hc] at h2
    have h3 := hY g hg
    have h4 : D.r D.g₀ * κ g' * D.r D.g₀⁻¹ + D.r D.g₀ * la g' * D.r D.g₀⁻¹
        = D.r g * Z * D.r g⁻¹ - Z := by
      rw [← add_mul, ← mul_add, hY g' hg', dTw, one_smul, mul_sub, sub_mul, hZ]
      congr 1
      calc D.r D.g₀ * (D.r g' * Y * D.r g'⁻¹) * D.r D.g₀⁻¹
          = (D.r D.g₀ * D.r g') * Y * (D.r g'⁻¹ * D.r D.g₀⁻¹) := by simp only [mul_assoc]
        _ = (D.r g * D.r D.g₀) * Y * (D.r D.g₀⁻¹ * D.r g⁻¹) := by
          rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, e, e']
        _ = _ := by simp only [mul_assoc]
    have h5 : (c - 1) • κ g = (c - 1) • dTw (fun _ => 1) D.r Y₁ g := by
      simp only [dTw, one_smul] at h1 h2 h3 ⊢
      rw [hY₁, smul_sub, mul_smul_comm, smul_mul_assoc, smul_inv_smul₀ hc1, smul_inv_smul₀ hc1]
      simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
      linear_combination (norm := module) c • h4 - c • h1 - h2 - h3
    exact smul_right_injective _ hc1 h5
  refine ⟨⟨Y₁, key⟩, Y - Y₁, fun g hg => ?_⟩
  have h3 := hY g hg
  rw [key g hg] at h3
  simp only [dTw, one_smul, mul_sub, sub_mul] at h3 ⊢
  rw [← sub_eq_zero] at h3 ⊢
  rw [← h3]; abel
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.BlockPrinc

section

@[expose] public section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem coc_comb {F G : Type} [Field F] [Group G] {n m : ℕ} (χ : G → F)
    (r : G → Matrix (Fin n) (Fin n) F) (z : Fin m → G → Matrix (Fin n) (Fin n) F) (α : Fin m → F)
    (hz : ∀ k, TwCoc χ r Set.univ (z k)) : TwCoc χ r Set.univ fun g => ∑ k, α k • z k g := by
  intro g _ h _
  show ∑ k, α k • z k (g * h) = ∑ k, α k • z k g + χ g • (r g * (∑ k, α k • z k h) * r g⁻¹)
  rw [Finset.sum_congr rfl fun k _ => by rw [hz k g (Set.mem_univ _) h (Set.mem_univ _)]]
  simp [smul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_comm]

private theorem cut_mul {F : Type} [Field F] {n : ℕ} (p q : Fin n → Prop) [∀ i j, Decidable (p i ∧ q j)]
    (Z B : Matrix (Fin n) (Fin n) F) (hB : ∀ k j, ¬ (q k ↔ q j) → B k j = 0) (i j : Fin n) :
    ((Matrix.of fun i j => if p i ∧ q j then Z i j else 0) * B) i j = if p i ∧ q j then (Z * B) i j else 0 := by
  simp only [Matrix.mul_apply, Matrix.of_apply]
  split_ifs with h
  · refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : q k ↔ q j
    · rw [if_pos ⟨h.1, hk.2 h.2⟩]
    · rw [hB k j hk, mul_zero, mul_zero]
  · refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : q k ↔ q j
    · rw [if_neg (fun h' => h ⟨h'.1, hk.1 h'.2⟩), zero_mul]
    · rw [hB k j hk, mul_zero]

private theorem kills_cut {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n)
    (p q : Fin n → Prop) [∀ i j, Decidable (p i ∧ q j)] (z : G → Matrix (Fin n) (Fin n) F)
    (hq : ∀ k j, ¬ (q k ↔ q j) → ¬ ((k : ℕ) < D.a ↔ (j : ℕ) < D.a))
    (hk : ∀ i j, p i → q j → D.KillsRel z i j) (i j : Fin n) :
    D.KillsRel (fun g => Matrix.of fun i j => if p i ∧ q j then z g i j else 0) i j := by
  intro c hc hs
  have hev : ∀ g k l, ¬ (q k ↔ q l) → D.r g k l = 0 := by
    intro g k l h
    exact (Submodule.mem_bot F).1 (((D.ev g) k l).2 (hq k l h))
  have e : ∀ g, ((Matrix.of fun i j => if p i ∧ q j then z g i j else 0) * D.r g) i j
      = if p i ∧ q j then (z g * D.r g) i j else 0 := fun g => cut_mul p q (z g) (D.r g) (hev g) i j
  simp only [Finsupp.sum, Matrix.sum_apply, Matrix.smul_apply, e]
  split_ifs with h
  · have := hk i j h.1 h.2 c hc hs
    simpa [Finsupp.sum, Matrix.sum_apply] using this
  · simp

private theorem block_princ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n)
    (K L : G → Matrix (Fin n) (Fin n) F) (hK : TwCoc (fun _ => 1) D.r Set.univ K)
    (hL : TwCoc D.χF D.r Set.univ L) (hKo : ∀ g, K g ∈ Od F F n D.a) (hLo : ∀ g, L g ∈ Od F F n D.a)
    (hk : ∀ i j, D.KillsRel (fun g => K g + L g) i j) :
    (∃ Y, ∀ g, K g = dTw (fun _ => 1) D.r Y g) ∧ ∃ Y, ∀ g, L g = dTw D.χF D.r Y g := by
  have hKL : TwCoc (fun _ => (1 : F)) D.r D.G' (fun g => K g + L g) := by
    intro g hg h _
    have e1 : K (g * h) = K g + D.r g * K h * D.r g⁻¹ := by simpa using hK g trivial h trivial
    have e2 : L (g * h) = L g + D.r g * L h * D.r g⁻¹ := by
      simpa [DetFr.χF, D.χ_triv g hg] using hL g trivial h trivial
    show K (g * h) + L (g * h) = K g + L g + (1 : F) • (D.r g * (K h + L h) * D.r g⁻¹)
    rw [e1, e2, one_smul, Matrix.mul_add, Matrix.add_mul]
    abel
  obtain ⟨Y, hY⟩ := Det.der D _ hKL hk
  obtain ⟨⟨Y1, hY1⟩, ⟨Y2, hY2⟩⟩ := Det.eigen D K L Y hK hL hY
  have hχ1 : ∀ g ∈ D.G', D.χF g = 1 := by intro g hg; simp [DetFr.χF, D.χ_triv g hg]
  have hY2' : ∀ g ∈ D.G', L g = dTw D.χF D.r Y2 g := by
    intro g hg
    rw [hY2 g hg]
    simp [dTw, hχ1 g hg]
  obtain ⟨Z1, -, hZ1⟩ := Det.infres D (fun _ => 1) K Y1 (by intros; simp) (by intros; rfl) hK hKo hY1
  obtain ⟨Z2, -, hZ2⟩ := Det.infres D D.χF L Y2 (by intro g h; simp [DetFr.χF]) hχ1 hL hLo hY2'
  exact ⟨⟨Z1, hZ1⟩, ⟨Z2, hZ2⟩⟩

theorem UpperTheory.V.Pa.Det.ann :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) {m : ℕ} (κ la : Fin m → G → Matrix (Fin n) (Fin n) F) (s : F) (ph : G → Matrix (Fin n) (Fin n) F), D.IsKap κ → D.IsTw κ s ph la → ∀ (α β : Fin m → F) (i j : Fin n), ¬ (((i : ℕ) < D.a) ↔ ((j : ℕ) < D.a)) → D.KillsRel (fun g => ∑ k, α k • κ k g + ∑ k, β k • la k g) i j → α = 0 ∧ ∃ Y ∈ Od F F n D.a, s • Yᵀ = Y ∧ ∀ g, ∑ k, β k • la k g = dTw D.χF D.r Y g := by
  classical
  intro F G _ _ n D m κ la s ph hκ hla α β i j hij hkill
  obtain ⟨K, hKe⟩ : ∃ K : G → Matrix (Fin n) (Fin n) F, K = fun g => ∑ k, α k • κ k g := ⟨_, rfl⟩
  obtain ⟨L, hLe⟩ : ∃ L : G → Matrix (Fin n) (Fin n) F, L = fun g => ∑ k, β k • la k g := ⟨_, rfl⟩
  rw [show (fun g => ∑ k, α k • κ k g + ∑ k, β k • la k g) = fun g => K g + L g by rw [hKe, hLe]] at hkill
  have hKc : TwCoc (fun _ => (1 : F)) D.r Set.univ K := by rw [hKe]; exact coc_comb _ _ κ α hκ.coc
  have hLc : TwCoc D.χF D.r Set.univ L := by rw [hLe]; exact coc_comb _ _ la β hla.coc
  have hKo : ∀ g, K g ∈ Od F F n D.a := fun g => by
    rw [hKe]; exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hκ.od k g)
  have hLo : ∀ g, L g ∈ Od F F n D.a := fun g => by
    rw [hLe]; exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hla.od k g)
  have hKp : ∀ g, K (D.σ g) = (-1 : F) • (K g)ᵀ := by
    intro g; rw [hKe]; simp [hκ.pol, Matrix.transpose_sum]
  have hLp : ∀ g, L (D.σ g) = s • (L g)ᵀ := by
    intro g; rw [hLe]; simp [hla.pol, Matrix.transpose_sum, Finset.smul_sum, smul_smul, mul_comm]
  have hTot : TwCoc (fun _ => (1 : F)) D.r D.G' (fun g => K g + L g) := by
    intro g hg h _
    have e1 : K (g * h) = K g + D.r g * K h * D.r g⁻¹ := by simpa using hKc g trivial h trivial
    have e2 : L (g * h) = L g + D.r g * L h * D.r g⁻¹ := by
      simpa [DetFr.χF, D.χ_triv g hg] using hLc g trivial h trivial
    show K (g * h) + L (g * h) = K g + L g + (1 : F) • (D.r g * (K h + L h) * D.r g⁻¹)
    rw [e1, e2, one_smul, Matrix.mul_add, Matrix.add_mul]
    abel
  obtain ⟨p, hpd⟩ : ∃ p : Fin n → Prop, ∀ x, p x ↔ ((x : ℕ) < D.a ↔ (i : ℕ) < D.a) := ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨q, hqd⟩ : ∃ q : Fin n → Prop, ∀ x, q x ↔ ((x : ℕ) < D.a ↔ (j : ℕ) < D.a) := ⟨_, fun _ => Iff.rfl⟩
  have hq : ∀ k l, ¬ (q k ↔ q l) → ¬ ((k : ℕ) < D.a ↔ (l : ℕ) < D.a) := by
    intro k l h h'
    apply h
    rw [hqd k, hqd l]
    tauto
  have hk' : ∀ i' j', p i' → q j' → D.KillsRel (fun g => K g + L g) i' j' := fun i' j' hi' hj' =>
    Det.relMove D _ i j hTot hkill i' j' ((hpd i').1 hi').symm ((hqd j').1 hj').symm
  have cK := Det.cornerCoc D _ _ _ hKc
  have cL := Det.cornerCoc D _ _ _ hLc
  have hcase : ((i : ℕ) < D.a ∧ ¬ (j : ℕ) < D.a) ∨ (¬ (i : ℕ) < D.a ∧ (j : ℕ) < D.a) := by tauto
  have key : ∃ Y1 Y2, ((∀ g, cV D.a (K g) = dTw (fun _ => (1 : F)) D.r Y1 g) ∨
      (∀ g, cV' D.a (K g) = dTw (fun _ => (1 : F)) D.r Y1 g)) ∧
      ((∀ g, cV D.a (L g) = dTw D.χF D.r Y2 g) ∨ (∀ g, cV' D.a (L g) = dTw D.χF D.r Y2 g)) := by
    rcases hcase with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · have hc2 : ∀ i' j', D.KillsRel (fun g => cV D.a (K g) + cV D.a (L g)) i' j' := by
        intro i' j'
        rw [show (fun g => cV D.a (K g) + cV D.a (L g)) =
            fun g => Matrix.of fun a b => if p a ∧ q b then (K g + L g) a b else 0 by
          funext g
          ext a b
          have hpa : p a ↔ (a : ℕ) < D.a := by rw [hpd]; tauto
          have hqb : q b ↔ ¬ (b : ℕ) < D.a := by rw [hqd]; tauto
          simp only [cV, Matrix.of_apply, Matrix.add_apply]
          split_ifs <;> first | rfl | (exfalso; tauto) | simp]
        exact kills_cut D p q (fun g => K g + L g) hq hk' i' j'
      obtain ⟨⟨Y1, hY1⟩, ⟨Y2, hY2⟩⟩ := block_princ D (fun g => cV D.a (K g)) (fun g => cV D.a (L g))
        cK.1 cL.1 (fun g => (cK.2.2.2 (K g)).1) (fun g => (cL.2.2.2 (L g)).1) hc2
      exact ⟨Y1, Y2, Or.inl hY1, Or.inl hY2⟩
    · have hc2 : ∀ i' j', D.KillsRel (fun g => cV' D.a (K g) + cV' D.a (L g)) i' j' := by
        intro i' j'
        rw [show (fun g => cV' D.a (K g) + cV' D.a (L g)) =
            fun g => Matrix.of fun a b => if p a ∧ q b then (K g + L g) a b else 0 by
          funext g
          ext a b
          have hpa : p a ↔ ¬ (a : ℕ) < D.a := by rw [hpd]; tauto
          have hqb : q b ↔ (b : ℕ) < D.a := by rw [hqd]; tauto
          simp only [cV', Matrix.of_apply, Matrix.add_apply]
          split_ifs <;> first | rfl | (exfalso; tauto) | simp]
        exact kills_cut D p q (fun g => K g + L g) hq hk' i' j'
      obtain ⟨⟨Y1, hY1⟩, ⟨Y2, hY2⟩⟩ := block_princ D (fun g => cV' D.a (K g)) (fun g => cV' D.a (L g))
        cK.2.1 cL.2.1 (fun g => (cK.2.2.2 (K g)).2.1) (fun g => (cL.2.2.2 (L g)).2.1) hc2
      exact ⟨Y1, Y2, Or.inr hY1, Or.inr hY2⟩
  obtain ⟨Y1, Y2, hK1, hL2⟩ := key
  obtain ⟨YK, hYKo, hYKs, hYK⟩ :=
    Det.shapiro D (fun _ => (1 : F)) (-1) K Y1 (fun _ => rfl) (by norm_num) hKc hKo hKp hK1
  obtain ⟨YL, hYLo, hYLs, hYL⟩ :=
    Det.shapiro D D.χF s L Y2 (fun g => by simp [DetFr.χF, D.χσ]) hla.sq hLc hLo hLp hL2
  have hT : YKᵀ = -YK := by
    have h := congrArg Matrix.transpose hYKs
    simp only [Matrix.transpose_smul, Matrix.transpose_transpose, neg_smul, one_smul] at h
    exact h.symm
  have hα : α = 0 := hκ.indep α YK hYKo hT fun g => by
    have := hYK g
    rw [hKe] at this
    exact this
  exact ⟨hα, YL, hYLo, hYLs, fun g => by
    have := hYL g
    rw [hLe] at this
    exact this⟩
end
end
