module

public import Formalism.HermitianCurvature.StatementTBB
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CkOnInCCCongrOnGroup
public import Formalism.HermitianCurvature.LetterProductDoubleDegreeCount
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BetaCapelliSymmOfXiExists
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BetaFinsetSumSmulOfXiExists
public import Formalism.HermitianCurvature.StatementB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.RealPlaceAnalysis.StatementA
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimE

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.BetaSelfReNonneg

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset MeasureTheory

namespace GlobalTheory.BetaPos

theorem bcWeight_nonneg' (k r : ℕ) (T T' : ℝ) (q : (Fin r → ℂ) × ℂ) : 0 ≤ bcWeight k r T T' q := by
  unfold bcWeight
  split_ifs with h
  · exact mul_nonneg (Finset.prod_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _) (pow_nonneg (sub_nonneg.2 h) _)
  · exact le_rfl

theorem beta_self_re_nonneg : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)), 0 ≤ (B.beta D F F).re := by
  intro k r Wp Wq _ _ _ _ _ _ D F
  have hβ : B.beta D F F = ∫ q : (Fin r → ℂ) × ℂ, ((bcWeight k r (Tz k r D.z) (Tz k r D.z') q *
      ‖B.hsVec (B.JF D F (bigCell k r q.1 (D.μsec q.2)))‖ ^ 2 : ℝ) : ℂ) := by
    unfold B.beta betaBig
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only []
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [hβ, integral_complex_ofReal, Complex.ofReal_re]
  exact integral_nonneg fun q => mul_nonneg (bcWeight_nonneg' _ _ _ _ _) (sq_nonneg _)

end GlobalTheory.BetaPos
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.FoldrCapelliSumEigen

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

section
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem smoothLev_finsum_smul {ι : Type} (t : Finset ι) (c : ι → ℂ) (f : ι → B.Mat k r → E)
    (hf : ∀ i, Q.SmoothLev k r 0 Set.univ (f i)) :
    Q.SmoothLev k r 0 Set.univ (fun y => ∑ i ∈ t, c i • f i y) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using Formalism.FourierDecayAlt.P.Qx2.smooth_zero
  | insert a t ha ih =>
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', he⟩ := ih g₀ hg₀
    obtain ⟨V, h', hV, hgV, hh', he'⟩ := hf a g₀ hg₀
    refine ⟨U ∩ V, fun y => c a • h' y + f' y, hU.inter hV, ⟨hgU, hgV⟩,
      ((hh'.mono Set.inter_subset_right).const_smul (c a)).add (hf'.mono Set.inter_subset_left), ?_⟩
    intro g hg hgG
    beta_reduce
    rw [Finset.sum_insert ha, he' g hg.2 hgG, ← he g hg.1 hgG]

theorem capelli_finsum_smul {ι : Type} (t : Finset ι) (c : ι → ℂ) (f : ι → B.Mat k r → E)
    (hf : ∀ i, Q.SmoothLev k r 0 Set.univ (f i)) (Y : ℂ) {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    Q.CV k r Y (fun y => ∑ i ∈ t, c i • f i y) g = ∑ i ∈ t, c i • Q.CV k r Y (f i) g := by
  classical
  have hT := Formalism.FourierDecayAlt.P.Dx1.LZ.good_CV (k := k) (r := r) (E := E) Y
  have hg' := Formalism.FourierDecayAlt.P.Dx1.LZ.glev0 hg
  induction t using Finset.induction_on with
  | empty => simpa using hT.map_zero hg'
  | insert a t ha ih =>
    have h := hT.lin _ (f a) (c a) (smoothLev_finsum_smul t c f hf) (hf a) g hg'
    simp only [Finset.sum_insert ha]
    rw [← ih, add_comm, ← h]
    congr 1
    funext y
    rw [add_comm]

end

theorem foldr_capelli_sum_eigen : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ev : Fin N₀ → ℝ → ℂ) (s : ℂ) (F : B.Mat k r → (Wq →L[ℂ] Wp)), (∀ i, B.CkOn ⊤ (B.GV k r) (Fi i)) → (∀ i (Y : ℝ), ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ev i Y • Fi i g) → (∀ g ∈ B.GV k r, F g = ∑ i, Fi i g) → ∀ w : List (Bool × ℝ), ∀ g ∈ B.GV k r, (w.foldr (fun a H => s • Q.CV k r (a.2 : ℂ) H) F) g = ∑ i, (w.map fun a => s * ev i a.2).prod • Fi i g := by
  intro k r Wp Wq _ _ _ _ _ _ N₀ Fi ev s F hs hev hF w
  induction w with
  | nil => intro g hg; simpa using hF g hg
  | cons a w ih =>
    intro g hg
    have hT := Formalism.FourierDecayAlt.P.Dx1.LZ.good_CV (k := k) (r := r) (E := Wq →L[ℂ] Wp) (a.2 : ℂ)
    have h1 := hT.loc _ _ (fun y hy => ih y hy.1.1) g (Formalism.FourierDecayAlt.P.Dx1.LZ.glev0 hg)
    have h2 := capelli_finsum_smul Finset.univ (fun i => (w.map fun a => s * ev i a.2).prod) Fi
      (fun i => Formalism.FourierDecayAlt.P.Dx1.LZ.smooth_of_ck (hs i)) (a.2 : ℂ) hg
    simp only [List.foldr_cons, List.map_cons, List.prod_cons, Pi.smul_apply]
    rw [h1.trans h2, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hev i a.2 g hg, smul_smul, smul_smul]
    congr 1
    ring

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.GramBlockDiagonalEnergyBound

section

@[expose] public section

open Formalism.REAL Finset

namespace GlobalTheory

theorem abs_list_prod_map_le_of_abs_le {α : Type} (L : List α) (f n : α → ℝ)
    (h : ∀ a ∈ L, |f a| ≤ n a) : |(L.map f).prod| ≤ (L.map n).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, abs_mul]
    have h1 := h a (by simp)
    have h2 := ih (fun b hb => h b (by simp [hb]))
    exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)

theorem sum_weight_blockDiagonal_eq {ι κ : Type} [Fintype ι] [DecidableEq κ] (B : ι → ι → ℂ)
    (k : ι → κ) (hB : ∀ i j, k i ≠ k j → B i j = 0) (f : κ → ℝ) :
    (∑ i, ∑ j, ((f (k i) : ℝ) : ℂ) * B i j).re =
      ∑ t ∈ Finset.univ.image k, f t *
        (∑ i ∈ Finset.univ.filter (fun i => k i = t),
          ∑ j ∈ Finset.univ.filter (fun j => k j = t), B i j).re := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image k) (g := k)
    (fun i _ => Finset.mem_image_of_mem k (Finset.mem_univ i)), Complex.re_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [← Complex.re_ofReal_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : k i = t := (Finset.mem_filter.mp hi).2
  rw [← Finset.mul_sum, hi', Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs with h
  · rfl
  · exact hB i j (fun e => h (e ▸ hi'))

theorem gram_blockDiagonal_energy_bound :
    ∀ (ι α : Type) [Fintype ι] (B : ι → ι → ℂ) (c : ι → α → ℝ) (L : List α) (n : α → ℝ), (∀ S : Finset ι, 0 ≤ (∑ i ∈ S, ∑ j ∈ S, B i j).re) → (∀ i j, ∀ a ∈ L, c i a ≠ c j a → B i j = 0) → (∀ i, ∀ a ∈ L, |c i a| ≤ n a) → (∑ i, ∑ j, (((L.map (c i)).prod : ℝ) : ℂ) * B i j).re ≤ (L.map n).prod * (∑ i, ∑ j, B i j).re := by
  intro ι α _ B c L n hpos hzero hbd
  classical
  have hB : ∀ i j, L.map (c i) ≠ L.map (c j) → B i j = 0 := by
    intro i j hij
    by_contra hne
    apply hij
    refine List.map_congr_left (fun a ha => ?_)
    by_contra h
    exact hne (hzero i j a ha h)
  have e1 := sum_weight_blockDiagonal_eq B (fun i => L.map (c i)) hB List.prod
  have e2 := sum_weight_blockDiagonal_eq B (fun i => L.map (c i)) hB (fun _ => 1)
  simp only [Complex.ofReal_one, one_mul] at e2
  rw [e1, e2, Finset.mul_sum]
  refine Finset.sum_le_sum (fun t ht => ?_)
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
  exact mul_le_mul_of_nonneg_right
    ((le_abs_self _).trans (abs_list_prod_map_le_of_abs_le L (c i) n (hbd i))) (hpos _)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroEnergyLeOfEigenSum

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

theorem levelZero_energy_le_of_eigen_sum :
    GlobalTheory.HCXi.BesselXiIntegrable → ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (lam : Fin (2 * r + k + 1) → ℝ) (d : ℕ) (A : ℝ) (s : ℂ) (nn : ℝ → ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)), (s = 1 ∨ s = -1) → B.AB k r ≤ A → (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (F) g = ∑ i, Fi i g) → (∀ y : ℝ, ∏ t, (|y + lam t| + (d : ℝ)) ≤ nn y) → ∀ w : List (Bool × ℝ), (C7.principalHermitianLattice D s w F).re ≤ (w.map fun l => nn l.2).prod * (B.beta D F F).re := by
  intro hXi k r Wp Wq _ _ _ _ _ _ D lam d A s nn F hs hA hex hnn w
  obtain ⟨N₀, Fi, ν, hν, hcl, hev, hF⟩ := hex
  obtain ⟨σ, hσs, hσ⟩ : ∃ σ : ℝ, s = (σ : ℂ) ∧ |σ| = 1 := by
    rcases hs with h | h
    · exact ⟨1, by simp [h], by simp⟩
    · exact ⟨-1, by simp [h], by simp⟩
  have h5 : ∀ i, B.InCC A 5 (Fi i) := fun i => (hcl i).2 5
  set e : Fin N₀ → ℝ → ℝ := fun i Y => ∏ t, (Y + lam t + (ν i t : ℝ)) with he
  set c : Fin N₀ → Bool × ℝ → ℝ := fun i a => σ * e i a.2 with hc
  have hF1 : ∀ g ∈ B.GV k r, F g = ∑ i ∈ Finset.univ, (1 : ℂ) • Fi i g := by
    intro g hg; simpa using hF g hg
  have hfold := GlobalTheory.foldr_capelli_sum_eigen k r Wp Wq N₀ Fi (fun i Y => ((e i Y : ℝ) : ℂ)) s F (fun i => (hcl i).1)
    (fun i Y g hg => hev i Y g hg) hF w
  have e1 := GlobalTheory.beta_finset_sum_smul_of_bessel hXi k r Wp Wq D A (Fin N₀) Finset.univ Finset.univ _ (fun _ => 1) Fi _ F hA h5 hfold hF1
  have e2 := GlobalTheory.beta_finset_sum_smul_of_bessel hXi k r Wp Wq D A (Fin N₀) Finset.univ Finset.univ (fun _ => 1) (fun _ => 1) Fi F F hA h5
    hF1 hF1
  have hcast : ∀ i, (w.map fun a => s * ((e i a.2 : ℝ) : ℂ)).prod = (((w.map (c i)).prod : ℝ) : ℂ) := by
    intro i
    have : ∀ v : List (Bool × ℝ),
        (v.map fun a => s * ((e i a.2 : ℝ) : ℂ)).prod = (((v.map (c i)).prod : ℝ) : ℂ) := by
      intro v
      induction v with
      | nil => simp
      | cons a v ih =>
        rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, hσs]
        simp only [hc, Complex.ofReal_mul]
    exact this w
  have key := gram_blockDiagonal_energy_bound (Fin N₀) (Bool × ℝ) (fun i j => B.beta D (Fi i) (Fi j)) c w
    (fun l => nn l.2) ?_ ?_ ?_
  · unfold C7.principalHermitianLattice
    rw [e1, e2]
    simp only [star_one, mul_one, one_mul, hcast]
    exact key
  · intro S
    have e3 := GlobalTheory.beta_finset_sum_smul_of_bessel hXi k r Wp Wq D A (Fin N₀) S S (fun _ => 1) (fun _ => 1) Fi
      (fun g => ∑ i ∈ S, (1 : ℂ) • Fi i g) (fun g => ∑ i ∈ S, (1 : ℂ) • Fi i g) hA h5
      (fun _ _ => rfl) (fun _ _ => rfl)
    have e4 := GlobalTheory.BetaPos.beta_self_re_nonneg k r Wp Wq D (fun g => ∑ i ∈ S, (1 : ℂ) • Fi i g)
    rw [e3] at e4
    simpa only [star_one, mul_one, one_mul] using e4
  · intro i j a _ hne
    have hne' : e i a.2 ≠ e j a.2 := fun h => hne (by simp only [hc, h])
    have hsym := GlobalTheory.beta_capelli_symm_of_bessel hXi k r Wp Wq D a.2 A (Fi i) (Fi j) hA (hcl i) (hcl j)
    have h1 := GlobalTheory.beta_finset_sum_smul_of_bessel hXi k r Wp Wq D A (Fin N₀) {i} {j}
      (fun _ => ((e i a.2 : ℝ) : ℂ)) (fun _ => 1) Fi (Q.CV k r (a.2 : ℂ) (Fi i)) (Fi j) hA h5
      (fun g hg => by rw [Finset.sum_singleton]; exact hev i a.2 g hg) (fun g _ => by simp)
    have h2 := GlobalTheory.beta_finset_sum_smul_of_bessel hXi k r Wp Wq D A (Fin N₀) {i} {j}
      (fun _ => 1) (fun _ => ((e j a.2 : ℝ) : ℂ)) Fi (Fi i) (Q.CV k r (a.2 : ℂ) (Fi j)) hA h5
      (fun g _ => by simp) (fun g hg => by rw [Finset.sum_singleton]; exact hev j a.2 g hg)
    simp only [Finset.sum_singleton, star_one, mul_one, one_mul,
      Complex.star_def, Complex.conj_ofReal] at h1 h2
    rw [h1, h2] at hsym
    have hcc : ((e i a.2 : ℂ) - (e j a.2 : ℂ)) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne')
    have h0 : ((e i a.2 : ℂ) - (e j a.2 : ℂ)) * B.beta D (Fi i) (Fi j) = 0 := by
      rw [sub_mul, hsym, sub_self]
    exact (mul_eq_zero.mp h0).resolve_left hcc
  · intro i a _
    refine le_trans ?_ (hnn a.2)
    simp only [hc, he, abs_mul, hσ, one_mul, Finset.abs_prod]
    refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun t _ => (abs_add_le _ _).trans ?_)
    have : |(ν i t : ℝ)| ≤ (d : ℝ) := by exact_mod_cast hν i t
    linarith

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroFormLeNormCOfEigenSum

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory


open scoped Matrix.Norms.Elementwise in
theorem ckOn_group_finset_sum {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type}
    (s : Finset ι) (Fi : ι → B.Mat k r → E) (h : ∀ i, B.CkOn ⊤ (B.GV k r) (Fi i)) :
    B.CkOn ⊤ (B.GV k r) (fun g => ∑ i ∈ s, Fi i g) := by
  intro g₀ hg₀
  choose U f hU hgU hf hff using fun i => h i g₀ hg₀
  refine ⟨⋂ i ∈ s, U i, fun g => ∑ i ∈ s, f i g, isOpen_biInter_finset fun i _ => hU i,
    Set.mem_iInter₂.2 fun i _ => hgU i, ?_, ?_⟩
  · exact ContDiffOn.sum fun i hi => (hf i).mono fun g hg => Set.mem_iInter₂.1 hg i hi
  · intro g hg hG
    exact Finset.sum_congr rfl fun i hi => hff i g (Set.mem_iInter₂.1 hg i hi) hG

theorem levelZero_form_le_normC_of_eigen_sum : GlobalTheory.HCXi.BesselXiIntegrable → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (d : ℕ) (A : ℝ) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ), B.AB P.k P.r ≤ A → (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * P.r + P.k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV P.k P.r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV P.k P.r, (F) g = ∑ i, Fi i g) → (∀ y : ℝ, ∏ t, (|y + lam t| + (d : ℝ)) ≤ nn y) → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → (p.RR F 0 w [] []).re ≤ TBB.normC nn w * (B.beta p.T.base F F).re := by
  intro hXi Wp Wq _ _ _ _ _ _ P p lam d A nn F Y N hA hF hnn w hw _
  have hsm : B.CkOn ⊤ (B.GV P.k P.r) F := by
    obtain ⟨N₀, Fi, ν, -, hc, -, hsum⟩ := hF
    exact (ckOn_inCC_congr_on_group P.k P.r _ A (fun g => ∑ i, Fi i g) F
      (fun g hg => (hsum g hg).symm)).1 (ckOn_group_finset_sum Finset.univ Fi fun i => (hc i).1)
  have hs : M.sgn P p.l0 = 1 ∨ M.sgn P p.l0 = -1 := by
    unfold M.sgn
    exact neg_one_pow_eq_or ℂ _
  unfold KB.Pl.RR TBB.normC
  rw [Formalism.FourierDecayAlt.P.level_zero_holds _ _ _ _ _ _ _ _ _ _ _ hsm (Formalism.FourierDecayAlt.P.CutBP.good_positioned_of_cut hw.1)]
  exact GlobalTheory.levelZero_energy_le_of_eigen_sum hXi P.k P.r Wp Wq p.T.base lam d A _ nn F hs hA hF hnn w

end GlobalTheory
end
end
