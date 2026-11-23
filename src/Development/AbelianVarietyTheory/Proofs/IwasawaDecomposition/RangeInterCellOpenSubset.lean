module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellPointEqOfTriangularFramesStatement
import Mathlib.AlgebraicGeometry.Modules.Sheaf

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagCellOfNonvanishingLeadingMinors

section

@[expose] public section

noncomputable section

open Matrix

namespace GlobalTheory.FlagEmb.CellLU

variable {K : Type} [Field K] {n : ℕ}

theorem exists_lower_mul_upper (A : Matrix (Fin n) (Fin n) K)
    (hA : ∀ (k : ℕ) (h : k ≤ n), (A.submatrix (Fin.castLE h) (Fin.castLE h)).det ≠ 0) :
    ∃ L : Matrix (Fin n) (Fin n) K, (∀ i k, i < k → L i k = 0) ∧ (∀ i, L i i = 1) ∧
      ∀ i j, j < i → (L * A) i j = 0 := by
  have hw : ∀ i : Fin n, ∃ v : Fin i → K, vecMul v (A.submatrix (Fin.castLE i.isLt.le) (Fin.castLE i.isLt.le)) =
      fun j : Fin i => A i (Fin.castLE i.isLt.le j) := fun i =>
    ⟨vecMul (fun j : Fin i => A i (Fin.castLE i.isLt.le j))
      (A.submatrix (Fin.castLE i.isLt.le) (Fin.castLE i.isLt.le))⁻¹, by
      rw [vecMul_vecMul, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hA _ _)), vecMul_one]⟩
  choose v hv using hw
  refine ⟨Matrix.of fun i k => if h : (k : ℕ) < i then -v i ⟨k, h⟩ else if k = i then 1 else 0, ?_, ?_, ?_⟩
  · intro i k h
    simp only [Matrix.of_apply]
    rw [dite_eq_right (by have := Fin.lt_def.mp h; omega), if_neg (ne_of_gt h)]
  · intro i
    simp
  · intro i j h
    rw [Matrix.mul_apply]
    have hsplit : ∀ k : Fin n,
        (Matrix.of fun i k : Fin n => if h : (k : ℕ) < i then -v i ⟨k, h⟩ else if k = i then (1 : K) else 0) i k * A k j =
        (if h : (k : ℕ) < i then -v i ⟨k, h⟩ * A k j else 0) + (if k = i then A i j else 0) := by
      intro k
      simp only [Matrix.of_apply]
      rcases lt_trichotomy k i with h | h | h
      · have hk : (k : ℕ) < i := h
        rw [dite_eq_left hk, dite_eq_left hk, if_neg (ne_of_lt h), add_zero]
      · subst h; simp
      · have hk : ¬ (k : ℕ) < i := by have := Fin.lt_def.mp h; omega
        rw [dite_eq_right hk, dite_eq_right hk, if_neg (ne_of_gt h), if_neg (ne_of_gt h), zero_mul, add_zero]
    rw [Finset.sum_congr rfl fun k _ => hsplit k, Finset.sum_add_distrib, Finset.sum_ite_eq',
      if_pos (Finset.mem_univ _)]
    have hs : ∑ k : Fin i, -v i k * A (Fin.castLE i.isLt.le k) j =
        ∑ k : Fin n, (if h : (k : ℕ) < i then -v i ⟨k, h⟩ * A k j else 0) := by
      refine Fintype.sum_of_injective (Fin.castLE i.isLt.le) (Fin.castLE_injective _) _ _ (fun k hk => ?_)
        (fun k => by simp)
      rw [dite_eq_right]
      intro hlt
      exact hk ⟨⟨k, hlt⟩, Fin.ext rfl⟩
    rw [← hs]
    have hj := congrFun (hv i) ⟨j, h⟩
    simp only [vecMul, dotProduct, Matrix.submatrix_apply] at hj
    have hcj : Fin.castLE i.isLt.le (⟨j, h⟩ : Fin i) = j := Fin.ext rfl
    rw [hcj] at hj
    rw [← hj]
    simp only [neg_mul, Finset.sum_neg_distrib]
    ring

theorem exists_lu (A : Matrix (Fin n) (Fin n) K)
    (hA : ∀ (k : ℕ) (h : k ≤ n), (A.submatrix (Fin.castLE h) (Fin.castLE h)).det ≠ 0) :
    ∃ N b : Matrix (Fin n) (Fin n) K, (∀ i k, i < k → N i k = 0) ∧ (∀ i, N i i = 1) ∧
      (∀ i j, j < i → b i j = 0) ∧ (∀ i, b i i ≠ 0) ∧ A = N * b := by
  obtain ⟨L, hup, hd, hz⟩ := exists_lower_mul_upper A hA
  have hLt : L.BlockTriangular OrderDual.toDual := fun i k h => hup i k h
  have hL : L.det = 1 := by
    rw [Matrix.det_of_lowerTriangular L hLt]
    simp [hd]
  have hu : IsUnit L.det := by rw [hL]; exact isUnit_one
  letI := L.invertibleOfIsUnitDet hu
  have hN : L⁻¹.BlockTriangular OrderDual.toDual := blockTriangular_inv_of_blockTriangular hLt
  refine ⟨L⁻¹, L * A, fun i k h => hN h, fun i => ?_, hz, fun i => ?_, ?_⟩
  · have h1 : (L * L⁻¹) i i = 1 := by rw [mul_nonsing_inv _ hu]; simp
    rw [Matrix.mul_apply, Finset.sum_eq_single i, hd, one_mul] at h1
    · exact h1
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hN (show OrderDual.toDual i < OrderDual.toDual k from h), mul_zero]
      · rw [hup i k h, zero_mul]
    · simp
  · have h1 : (L * A).det ≠ 0 := by
      rw [det_mul, hL, one_mul]
      simpa using hA n le_rfl
    rw [Matrix.det_of_upperTriangular (fun i j h => hz i j h)] at h1
    exact Finset.prod_ne_zero_iff.1 h1 i (Finset.mem_univ _)
  · rw [← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]

theorem sum_lform_plk {S : Type} [CommRing S] {M k : ℕ} {ι ι' : Type} (D : ι' → Fin (M + 1) → S)
    (u : ι → Fin (M + 1) → S) (ρ : Fin k → ι') (e : Fin k → ι) :
    ∑ q, lform D ρ q * plk u e q = (Matrix.of fun l l' => ∑ r, D (ρ l') r * u (e l) r).det := by
  have h := Equiv.sum_comp (plE M k)
    (fun q : Fin k → Fin (M + 1) => (∏ l, D (ρ l) (q l)) * (Matrix.of fun l l' => u (e l) (q l')).det)
  refine Eq.trans h ?_
  simp only [det_apply', Matrix.of_apply, Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

theorem exists_cell (T : Type) (m : T → ℕ) (K : Type) [Field K] (M : ℕ) (D c u : Let m → Fin (M + 1) → K) (w : Pm m)
    (hD : LeftInv D c) (hu : InBlock c u)
    (h : ∀ τ j hj, ∑ q, lform D (wLet w ∘ std τ j hj) q * plk u (std τ j hj) q ≠ 0) :
    ∃ (x : CellVar m → K) (d : Let m → K), (∀ z, d z ≠ 0) ∧ Tri (cellVec c w x) u d := by
  have hA : ∀ τ, ∃ A : Matrix (Fin (m τ)) (Fin (m τ)) K, ∀ j, u ⟨τ, j⟩ = ∑ i, A i j • c ⟨τ, w τ i⟩ := fun τ => by
    have := fun j => (Submodule.mem_span_range_iff_exists_fun K).1 (hu ⟨τ, j⟩)
    choose a ha using this
    refine ⟨Matrix.of fun i j => a j (w τ i), fun j => ?_⟩
    rw [← ha j]
    exact (Equiv.sum_comp (w τ) (fun i => a j i • c ⟨τ, i⟩)).symm
  choose A hA using hA
  have hent : ∀ τ i j, ∑ r, D (wLet w ⟨τ, i⟩) r * u ⟨τ, j⟩ r = A τ i j := fun τ i j => by
    rw [hA]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ i', ∑ r, D (wLet w ⟨τ, i⟩) r * (A τ i' j * c ⟨τ, w τ i'⟩ r) = if i' = i then A τ i' j else 0 := by
      intro i'
      have h1 := hD (wLet w ⟨τ, i⟩) ⟨τ, w τ i'⟩
      rw [show (∑ r, D (wLet w ⟨τ, i⟩) r * (A τ i' j * c ⟨τ, w τ i'⟩ r)) =
        A τ i' j * ∑ r, D (wLet w ⟨τ, i⟩) r * c ⟨τ, w τ i'⟩ r by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring, h1]
      by_cases hi : i' = i
      · subst hi; simp [wLet]
      · rw [if_neg hi, if_neg, mul_zero]
        intro he
        simp only [wLet, Sigma.mk.injEq, heq_eq_eq, true_and] at he
        exact hi ((w τ).injective he).symm
    simp [this]
  have hmin : ∀ τ (k : ℕ) (hk : k ≤ m τ), ((A τ).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0 := by
    intro τ k hk
    have h1 := h τ k hk
    rw [sum_lform_plk, ← det_transpose] at h1
    convert h1 using 2
    ext l l'
    exact (hent τ _ _).symm
  choose N b hN hN1 hb hb1 hNb using fun τ => exists_lu (A τ) (hmin τ)
  refine ⟨fun y => N y.1 y.2.1.1 y.2.1.2, fun z => b z.1 z.2 z.2, fun z => hb1 _ _, ?_⟩
  have hcell : ∀ τ i j, cell (fun y : CellVar m => N y.1 y.2.1.1 y.2.1.2) τ i j = N τ i j := by
    intro τ i j
    unfold cell
    rcases lt_trichotomy i j with h | h | h
    · rw [dite_eq_right (not_lt.2 h.le), if_neg h.ne, hN τ i j h]
    · subst h; simp [hN1]
    · rw [dite_eq_left h]
  rintro ⟨τ, j⟩
  have hexp : u ⟨τ, j⟩ = ∑ k, b τ k j • cellVec c w (fun y : CellVar m => N y.1 y.2.1.1 y.2.1.2) ⟨τ, k⟩ := by
    rw [hA, hNb]
    simp only [cellVec, hcell, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  rw [hexp, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), add_sub_cancel_left]
  refine Submodule.sum_mem _ fun k hk => ?_
  rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hk) with h | h
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, h, rfl⟩)
  · rw [hb τ k j h, zero_smul]
    exact Submodule.zero_mem _

end GlobalTheory.FlagEmb.CellLU
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagCellOfNonvanishingLeadingMinorsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

theorem _root_.GlobalTheory.T.exists_flagCell_of_nonvanishing_leading_minors : ∀ (T : Type) (m : T → ℕ) (K : Type) [Field K] (M : ℕ) (D c u : Let m → Fin (M + 1) → K) (w : Pm m), LeftInv D c → InBlock c u → (∀ τ j hj, ∑ q, lform D (wLet w ∘ std τ j hj) q * plk u (std τ j hj) q ≠ 0) → ∃ (x : CellVar m → K) (d : Let m → K), (∀ z, d z ≠ 0) ∧ Tri (cellVec c w x) u d := by
  first | exact @GlobalTheory.FlagEmb.CellLU.exists_cell | exact GlobalTheory.FlagEmb.CellLU.exists_cell | (intros; apply GlobalTheory.FlagEmb.CellLU.exists_cell <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RangeInterCellOpenSubset

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb.Overlap

theorem spMap_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem exists_fieldPoint {A : Type} [CommRing A] (y : Sp A) :
    ∃ (k : Type) (_ : Field k) (ψ : A →+* k), ∀ q : Sp k, spMap ψ q = y := by
  refine ⟨(show PrimeSpectrum A from y).asIdeal.ResidueField, inferInstance, algebraMap _ _, fun q => ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap _ (show PrimeSpectrum _ from q).asIdeal = _
  rw [show (show PrimeSpectrum _ from q).asIdeal = ⊥ from Ideal.eq_bot_of_prime _]
  exact Ideal.ker_algebraMap_residueField _

theorem inBlock_cellVec {T : Type} {m : T → ℕ} {S : Type} [CommRing S] {ι : Type} {c c' : Let m → ι → S}
    (h : InBlock c c') (w : Pm m) (x : CellVar m → S) : InBlock c (cellVec c' w x) := fun z =>
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h ⟨z.1, w z.1 i⟩)

theorem map_lform {ι : Type} {M k : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (D : ι → Fin (M + 1) → S) (ρ : Fin k → ι) (q : Fin (plN M k + 1)) :
    φ (lform D ρ q) = lform (fun z => φ ∘ D z) ρ q := by
  simp [lform, map_prod]

theorem range_inter_cellOpen_subset : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsCover β s V α c D → IsPlk β s V α c p0 p h → ∀ b w (W : P.Opens), IsCellOpen p0 p (V b) (D b) w W → ∀ b' w', Set.range (h b' w') ∩ (W : Set P) ⊆ Set.range (h b w) := by
  intro O K _ _ β X s T _ m M B V α c D P p0 p h hc hp b w W hW b' w'
  rintro _ ⟨⟨y, rfl⟩, hy⟩
  obtain ⟨k, _, ψ', hψ'⟩ := exists_fieldPoint y
  have hz : ∀ q : Sp k, (spMap ψ' ≫ h b' w') q = h b' w' y := fun q => by
    rw [Scheme.Hom.comp_apply, hψ']
  obtain ⟨φ, hφ, hne⟩ := (hW k (spMap ψ' ≫ h b' w')).1 (by
    rintro _ ⟨q, rfl⟩
    rw [hz]; exact hy)
  rw [Category.assoc, hp.base] at hφ
  have hφ' : spMap φ ≫ (V b).2.fromSpec =
      spMap (ψ'.comp (MvPolynomial.C : Γ(X, (V b').1) →+* CR m (V b'))) ≫ (V b').2.fromSpec := by
    rw [← hφ, cbase, ← Category.assoc, spMap_spMap]
  have hu : InBlock (fun z => φ ∘ c b z) (fun z => ψ' ∘ uvec (c b') w' z) := by
    have := inBlock_cellVec (hc.compat k b b' φ _ hφ') w' (ψ' ∘ MvPolynomial.X)
    convert this using 2 with z
    exact map_cellVec ψ' _ w' _ z
  have span_range_comp_eq_top : ∀ {A B : Type} [CommRing A] [CommRing B] {n : ℕ}
      (v : Fin (n + 1) → A), Ideal.span (Set.range v) = ⊤ → (ψ : A →+* B) →
      Ideal.span (Set.range (ψ ∘ v)) = ⊤ := by
    intro A B _ _ n v hv ψ
    rw [Set.range_comp, ← Ideal.map_span, hv, Ideal.map_top]
  have spMap_pt : ∀ {O A B : Type} [CommRing O] [CommRing A] [CommRing B] {n : ℕ}
      (c : O →+* A) (v : Fin (n + 1) → A) (hv : Ideal.span (Set.range v) = ⊤) (ψ : A →+* B),
      spMap ψ ≫ pt c v hv = pt (ψ.comp c) (ψ ∘ v) (span_range_comp_eq_top v hv ψ) := by
    intro O A B _ _ _ n c v hv ψ
    letI := MvPolynomial.gradedAlgebra (σ := Fin (n + 1)) (R := O)
    refine (ProjPoint.SpecMap_ofHom _ _ _ ψ).trans ?_
    unfold pt
    congr 1
    exact MvPolynomial.ringHom_ext (fun r => by simp) (fun i => by simp)
  obtain ⟨x, d, hd, ht⟩ := GlobalTheory.T.exists_flagCell_of_nonvanishing_leading_minors T m k M _ _ _ w ((hc.inv b).map φ) hu (fun τ j hj => by
    obtain ⟨hv, e⟩ := hp.plk b' w' (stdEn τ j hj)
    have := hne τ j hj _ _ _ (by rw [Category.assoc, e, spMap_pt])
    rw [map_plk] at this
    simpa only [map_lform] using this)
  have hψ : ∀ z, (MvPolynomial.eval₂Hom φ x : CR m (V b) →+* k) ∘ uvec (c b) w z =
      cellVec (fun z => φ ∘ c b z) w x z := fun z => by
    refine (map_cellVec _ _ w _ z).trans ?_
    congr 1
    · funext z r; simp
    · funext r; simp
  have key := GlobalTheory.T.flagCell_point_eq_of_triangular_frames O K β X s T m M B V α c D P p0 p h hc hp k b b' w w' (MvPolynomial.eval₂Hom φ x) ψ' d
    (by rw [hφ, cbase, ← Category.assoc, spMap_spMap, MvPolynomial.eval₂Hom_comp_C]) hd
    (by simpa only [hψ] using ht)
  obtain ⟨q⟩ : Nonempty (Sp k) := inferInstanceAs (Nonempty (PrimeSpectrum k))
  exact ⟨spMap (MvPolynomial.eval₂Hom φ x : CR m (V b) →+* k) q, by
    rw [← hz q, ← key, Scheme.Hom.comp_apply]⟩

end GlobalTheory.FlagEmb.Overlap
end
end
