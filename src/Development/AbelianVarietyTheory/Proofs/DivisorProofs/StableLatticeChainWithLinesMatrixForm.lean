module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.LinearAlgebra.Dimension.Constructions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Formalism.PieriBlockIdeals.CapelliCentralEnveloping
import Formalism.PieriBlockIdeals.LemmaWFromLattice
import Formalism.PieriBlockIdeals.Statement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixFibreProductStableLatticeChainLineStatement
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.WeaklyAdmissibleFiltrations.Statement
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.PowerSeries.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixRangeEq

section

@[expose] public section

namespace GlobalTheory.MatrixRangeExistence

theorem exists_matrix_range_eq {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (n : ℕ) (ϖ : O) (N : Submodule O (Fin n → O)) (hϖ : ϖ ≠ 0)
    (hN : ∀ y : Fin n → O, (fun a : Fin n => ϖ * y a) ∈ N) :
    ∃ A : Matrix (Fin n) (Fin n) O,
      (∀ x : Fin n → O, x ∈ N ↔ ∃ u : Fin n → O, Matrix.mulVec A u = x) ∧ Matrix.det A ≠ 0 := by
  classical
  let f : (Fin n → O) →ₗ[O] N :=
    LinearMap.codRestrict N (ϖ • LinearMap.id) (fun y => hN y)
  have hf : Function.Injective f := by
    intro y z h
    have h' : ϖ • y = ϖ • z := congrArg Subtype.val h
    funext a
    exact mul_left_cancel₀ hϖ (congrFun h' a)
  have h1 : n ≤ Module.finrank O N := by
    have := LinearMap.finrank_le_finrank_of_injective hf
    simpa using this
  have h2 : Module.finrank O N ≤ n := by
    have := Submodule.finrank_le N
    simpa using this
  let b : Module.Basis (Fin n) O N := Module.finBasisOfFinrankEq O N (le_antisymm h2 h1)
  let A : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => (b j : Fin n → O) i
  have hA : ∀ u : Fin n → O, Matrix.mulVec A u = ((∑ j, u j • b j : N) : Fin n → O) := by
    intro u
    funext i
    simp [A, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have key : ∀ x : Fin n → O, x ∈ N ↔ ∃ u : Fin n → O, Matrix.mulVec A u = x := by
    intro x
    constructor
    · intro hx
      refine ⟨fun j => b.repr ⟨x, hx⟩ j, ?_⟩
      rw [hA, b.sum_repr ⟨x, hx⟩]
    · rintro ⟨u, rfl⟩
      rw [hA]
      exact Subtype.property _
  refine ⟨A, key, ?_⟩
  have hcol : ∀ j : Fin n, ∃ u : Fin n → O,
      Matrix.mulVec A u = fun a => ϖ * (Pi.single j (1 : O) : Fin n → O) a :=
    fun j => (key _).1 (hN _)
  choose U hU using hcol
  have hmul : A * (Matrix.of fun i j => U j i) = ϖ • (1 : Matrix (Fin n) (Fin n) O) := by
    ext i j
    have := congrFun (hU j) i
    simp only [Matrix.mulVec, dotProduct] at this
    simp [Matrix.mul_apply, this, Matrix.one_apply, Pi.single_apply]
  intro h0
  have := congrArg Matrix.det hmul
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at this
  exact pow_ne_zero _ hϖ this.symm

end GlobalTheory.MatrixRangeExistence
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareMatrixImageSubmoduleContainsUniformi

section

@[expose] public section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
open Matrix

namespace GlobalTheory

theorem exists_square_matrix_of_submodule_between
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n : ℕ) (ϖ : O)
    (N : Submodule O (Fin n → O)) (hϖ : ϖ ≠ 0)
    (hN : ∀ y : Fin n → O, (fun a => ϖ * y a) ∈ N) :
    ∃ A : Matrix (Fin n) (Fin n) O, (∀ x, x ∈ N ↔ ∃ u, A *ᵥ u = x) ∧ A.det ≠ 0 := by
  first
  | exact @_root_.GlobalTheory.MatrixRangeExistence.exists_matrix_range_eq
  | exact _root_.GlobalTheory.MatrixRangeExistence.exists_matrix_range_eq
  | (apply _root_.GlobalTheory.MatrixRangeExistence.exists_matrix_range_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.MatrixRangeExistence.exists_matrix_range_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MatrixRangeExistence.exists_matrix_range_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MatrixRangeExistence.exists_matrix_range_eq ..)
end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareMatrixImageSubmoduleContainsUniformiStatement

section

@[expose] public section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
open Matrix

theorem _root_.GlobalTheory.T.exists_square_matrix_image_submodule_contains_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n : ℕ) (ϖ : O) (N : Submodule O (Fin n → O)), ϖ ≠ 0 → (∀ y : Fin n → O, (fun a => ϖ * y a) ∈ N) → ∃ A : Matrix (Fin n) (Fin n) O, (∀ x, x ∈ N ↔ ∃ u, A *ᵥ u = x) ∧ A.det ≠ 0 := by
  first | exact @GlobalTheory.exists_square_matrix_of_submodule_between | exact GlobalTheory.exists_square_matrix_of_submodule_between | (intros; apply GlobalTheory.exists_square_matrix_of_submodule_between <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankResidueBasisMatrixSuccOfAdjoinVector

section

@[expose] public section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
open Matrix

namespace GlobalTheory

theorem rank_residue_succ_of_adjoin
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n : ℕ) (ϖ : O)
    (Ac As : Matrix (Fin n) (Fin n) O) (x : Fin n → O) :
    Irreducible ϖ → (∀ y : Fin n → O, ∃ u, Ac *ᵥ u = fun a => ϖ * y a) →
    (∀ w, ∃ u c, As *ᵥ w = Ac *ᵥ u + fun a => c * x a) → (∃ w, As *ᵥ w = x) →
    (∀ u, ∃ w, As *ᵥ w = Ac *ᵥ u) → (¬ ∃ u, Ac *ᵥ u = x) →
    (As.map (residue O)).rank = (Ac.map (residue O)).rank + 1 := by
  intro hϖ h1 h2 h3 h4 h5
  set bar := residue O with hbar
  have hmap : ∀ (A : Matrix (Fin n) (Fin n) O) (v : Fin n → O),
      (A.map bar) *ᵥ (bar ∘ v) = bar ∘ (A *ᵥ v) := by
    intro A v; funext i; exact (RingHom.map_mulVec bar A v i).symm
  have hlift : ∀ z : Fin n → ResidueField O, ∃ v : Fin n → O, bar ∘ v = z := by
    intro z
    refine ⟨fun i => (residue_surjective (z i)).choose, ?_⟩
    funext i; exact (residue_surjective (z i)).choose_spec
  set V := LinearMap.range (As.map bar).mulVecLin
  set Wc := LinearMap.range (Ac.map bar).mulVecLin
  set xb : Fin n → ResidueField O := bar ∘ x
  have hV : V = Wc ⊔ Submodule.span (ResidueField O) {xb} := by
    apply le_antisymm
    · rintro v ⟨z, rfl⟩
      obtain ⟨w, rfl⟩ := hlift z
      obtain ⟨u, c, hc⟩ := h2 w
      rw [Matrix.mulVecLin_apply, hmap, hc]
      have : bar ∘ (Ac *ᵥ u + fun a => c * x a) = (Ac.map bar) *ᵥ (bar ∘ u) + bar c • xb := by
        rw [hmap]; funext i; simp [xb]
      rw [this]
      exact Submodule.add_mem_sup ⟨bar ∘ u, rfl⟩
        (Submodule.smul_mem _ _ (Submodule.subset_span rfl))
    · apply sup_le
      · rintro v ⟨z, rfl⟩
        obtain ⟨u, rfl⟩ := hlift z
        obtain ⟨w, hw⟩ := h4 u
        refine ⟨bar ∘ w, ?_⟩
        rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, hmap, hmap, hw]
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        obtain ⟨w, hw⟩ := h3
        exact ⟨bar ∘ w, by rw [Matrix.mulVecLin_apply, hmap, hw]⟩
  have hxb : xb ∉ Wc := by
    rintro ⟨z, hz⟩
    obtain ⟨u, rfl⟩ := hlift z
    rw [Matrix.mulVecLin_apply, hmap] at hz
    have hmem : ∀ a, (x - Ac *ᵥ u) a ∈ Ideal.span {ϖ} := by
      intro a
      rw [← hϖ.maximalIdeal_eq, ← residue_eq_zero_iff]
      have := congrFun hz a
      simp only [Function.comp_apply, xb] at this
      rw [Pi.sub_apply, map_sub, ← hbar, this, sub_self]
    choose y hy using fun a => Ideal.mem_span_singleton'.1 (hmem a)
    obtain ⟨u', hu'⟩ := h1 y
    apply h5
    refine ⟨u + u', ?_⟩
    rw [Matrix.mulVec_add, hu']
    funext a
    have := hy a
    simp only [Pi.sub_apply] at this
    simp only [Pi.add_apply]
    rw [mul_comm, this]; ring
  have hxb0 : xb ≠ 0 := by
    intro h; exact hxb (h ▸ Wc.zero_mem)
  have hinf : Wc ⊓ Submodule.span (ResidueField O) {xb} = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvW, hvs⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hvs
    by_cases hc : c = 0
    · simp [hc]
    · exact absurd (by simpa [hc] using Wc.smul_mem c⁻¹ hvW) hxb
  have key := Submodule.finrank_sup_add_finrank_inf_eq Wc (Submodule.span (ResidueField O) {xb})
  rw [hinf, finrank_bot, add_zero, finrank_span_singleton hxb0, ← hV] at key
  rw [← Matrix.finrank_range_mulVecLin (As.map bar), ← Matrix.finrank_range_mulVecLin (Ac.map bar)]
  exact key

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankResidueBasisMatrixSuccOfAdjoinVectorStatement

section

@[expose] public section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
open Matrix

theorem _root_.GlobalTheory.T.rank_residue_basis_matrix_succ_of_adjoin_vector : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n : ℕ) (ϖ : O) (Ac As : Matrix (Fin n) (Fin n) O) (x : Fin n → O), Irreducible ϖ → (∀ y : Fin n → O, ∃ u, Ac *ᵥ u = fun a => ϖ * y a) → (∀ w, ∃ u c, As *ᵥ w = Ac *ᵥ u + fun a => c * x a) → (∃ w, As *ᵥ w = x) → (∀ u, ∃ w, As *ᵥ w = Ac *ᵥ u) → (¬ ∃ u, Ac *ᵥ u = x) → (As.map (residue O)).rank = (Ac.map (residue O)).rank + 1 := by
  first | exact @GlobalTheory.rank_residue_succ_of_adjoin | exact GlobalTheory.rank_residue_succ_of_adjoin | (intros; apply GlobalTheory.rank_residue_succ_of_adjoin <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableLatticeChainWithLinesMatrixForm

section

@[expose] public section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
open Matrix

set_option autoImplicit false

namespace GlobalTheory.WachChain

theorem cancel_left {O ι : Type} [CommRing O] [Fintype ι] {q m : ℕ} (A : Matrix ι (Fin q) O)
    (hA : Function.Injective A.mulVec) {X Y : Matrix (Fin q) (Fin m) O} (h : A * X = A * Y) : X = Y := by
  ext i j
  have h1 := congrArg (fun Z => Z *ᵥ Pi.single j 1) h
  simp only [← Matrix.mulVec_mulVec] at h1
  have h2 := congrFun (hA h1) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h2

theorem solve {O ι : Type} [CommRing O] [Fintype ι] {q m : ℕ} (A : Matrix ι (Fin q) O) (Z : Matrix ι (Fin m) O)
    (h : ∀ j, ∃ w, A *ᵥ w = fun i => Z i j) : ∃ Y : Matrix (Fin q) (Fin m) O, A * Y = Z := by
  choose w hw using h
  refine ⟨Matrix.of fun k j => w j k, ?_⟩
  ext i j
  have h1 := congrFun (hw j) i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using h1

theorem mkRep {Γ O ι : Type} [Group Γ] [CommRing O] [Fintype ι] [DecidableEq ι] {q : ℕ} (A : Matrix ι (Fin q) O)
    (ρ : Γ →* Matrix ι ι O) (hA : Function.Injective A.mulVec)
    (hst : ∀ g v, ∃ w, A *ᵥ w = ρ g *ᵥ (A *ᵥ v)) :
    ∃ r' : Γ →* GL (Fin q) O, ∀ g, A * (r' g : Matrix (Fin q) (Fin q) O) = ρ g * A := by
  have h1 : ∀ g, ∃ Y : Matrix (Fin q) (Fin q) O, A * Y = ρ g * A := fun g =>
    solve A (ρ g * A) fun j => by
      obtain ⟨w, hw⟩ := hst g (Pi.single j 1)
      refine ⟨w, ?_⟩
      rw [hw, Matrix.mulVec_mulVec]
      funext i
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  choose Y hY using h1
  let f : Γ →* Matrix (Fin q) (Fin q) O :=
    { toFun := Y
      map_one' := cancel_left A hA (by rw [hY, map_one, Matrix.one_mul, Matrix.mul_one])
      map_mul' := fun g h => cancel_left A hA (by
        rw [hY, map_mul, Matrix.mul_assoc, ← hY h, ← Matrix.mul_assoc, ← hY g, Matrix.mul_assoc]) }
  exact ⟨f.toHomUnits, fun g => by rw [MonoidHom.coe_toHomUnits]; exact hY g⟩

theorem chain_of_lattices : ∀ (Γ O : Type) [Group Γ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n t R : ℕ) (r : Γ →* GL (Fin n) O) (ψ : Fin t → Γ →* Oˣ) (ϖ : O) (M : Fin (R + 1) → Submodule O (Fin n → O)) (rs : Fin t → Fin R), Irreducible ϖ → (∀ x, x ∈ M 0 ↔ ∃ y : Fin n → O, x = fun a => ϖ * y a) → M (Fin.last R) = ⊤ → Monotone M → (∀ g k x, x ∈ M k → (r g : Matrix (Fin n) (Fin n) O).mulVec x ∈ M k) → (∀ s, ∃ x ∈ M (rs s).succ, x ∉ M (rs s).castSucc ∧ M (rs s).succ = M (rs s).castSucc ⊔ Submodule.span O {x} ∧ ∀ g, (r g : Matrix (Fin n) (Fin n) O).mulVec x - (fun a => ((ψ s g : Oˣ) : O) * x a) ∈ M (rs s).castSucc) → ∃ (x : GalMats Γ O n t R) (dim : Fin (R + 1) → ℕ), x.Chain (residue O) r (fun s => GlobalTheory.TripleGal.rk1 (ψ s)) rs dim ∧ dim 0 = 0 ∧ dim (Fin.last R) = n ∧ ∀ s, dim (rs s).succ = dim (rs s).castSucc + 1 := by
  intro Γ O _ _ _ _ n t R r ψ ϖ M rs hϖ hM0 hlast hmono hst hline
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hin : ∀ k (y : Fin n → O), (fun a => ϖ * y a) ∈ M k := fun k y =>
    hmono (Fin.zero_le k) ((hM0 _).2 ⟨y, rfl⟩)
  choose A hA hdet using fun k => GlobalTheory.T.exists_square_matrix_image_submodule_contains_uniformizer n ϖ (M k) hϖ0 (hin k)
  have hinj : ∀ k, Function.Injective (A k).mulVec := fun k u v huv => by
    by_contra hne
    refine hdet k ((Matrix.exists_mulVec_eq_zero_iff).1 ⟨u - v, sub_ne_zero.2 hne, ?_⟩)
    rw [Matrix.mulVec_sub, huv, sub_self]
  have hrep : ∀ k, ∃ ρ : Γ →* GL (Fin n) O, Tw ρ r (A k) := fun k =>
    mkRep (A k) ((Units.coeHom _).comp r) (hinj k)
      (fun g v => (hA k _).1 (hst g k _ ((hA k _).2 ⟨v, rfl⟩)))
  choose ρ hρ using hrep
  have hbb : ∀ k : Fin R, ∃ Y, A k.succ * Y = A k.castSucc := fun k =>
    solve _ _ fun j => (hA k.succ _).1 (hmono (Fin.castSucc_lt_succ (i := k)).le
      ((hA k.castSucc _).2 ⟨Pi.single j 1, by funext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]⟩))
  choose bb hbbe using hbb
  choose xs hxs hxn hsup hψ using hline
  have hsW : ∀ s w, ∃ u c', A (rs s).succ *ᵥ w = A (rs s).castSucc *ᵥ u + fun a => c' * xs s a := by
    intro s w
    have hm := (hA (rs s).succ _).2 ⟨w, rfl⟩
    rw [hsup s, Submodule.mem_sup] at hm
    obtain ⟨y, hy, z, hz, hyz⟩ := hm
    obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.1 hz
    obtain ⟨u, rfl⟩ := (hA _ _).1 hy
    exact ⟨u, c', by rw [← hyz]; rfl⟩
  have hxW : ∀ s, ∃ w, A (rs s).succ *ᵥ w = xs s := fun s => (hA _ _).1 (hxs s)
  have hcW : ∀ s u, ∃ w, A (rs s).succ *ᵥ w = A (rs s).castSucc *ᵥ u := fun s u =>
    (hA _ _).1 (hmono Fin.castSucc_lt_succ.le ((hA _ _).2 ⟨u, rfl⟩))
  have hnW : ∀ s, ¬ ∃ u, A (rs s).castSucc *ᵥ u = xs s := fun s h => hxn s ((hA _ _).2 h)
  have hψW : ∀ s g, ∃ u, A (rs s).castSucc *ᵥ u =
      (r g : Matrix (Fin n) (Fin n) O) *ᵥ xs s - fun a => ((ψ s g : Oˣ) : O) * xs s a :=
    fun s g => (hA _ _).1 (hψ s g)
  choose r2 B B' C E hL using fun s => GlobalTheory.T.matrix_fibre_product_stable_lattice_chain_line n r (ψ s) (A (rs s).castSucc) (A (rs s).succ) (ρ _) (ρ _)
    (xs s) (hinj _) (hinj _) (hρ _) (hρ _) (hsW s) (hxW s) (hcW s) (hψW s)
  refine ⟨⟨ρ, A, bb, r2, B, B', C, E⟩, fun k => ((A k).map (residue O)).rank,
    ⟨fun k => ⟨hρ k, hdet k, rfl⟩, fun k => ⟨?_, (hbbe k).symm⟩, fun s => hL s⟩, ?_, ?_,
    fun s => GlobalTheory.T.rank_residue_basis_matrix_succ_of_adjoin_vector n ϖ _ _ (xs s) hϖ (fun y => (hA _ _).1 (hin _ y)) (hsW s) (hxW s) (hcW s) (hnW s)⟩
  · intro g
    apply cancel_left (A k.succ) (hinj _)
    rw [← Matrix.mul_assoc, hbbe k, hρ k.castSucc g, ← hbbe k, ← Matrix.mul_assoc, ← hρ k.succ g,
      Matrix.mul_assoc]
  · have hz : (A 0).map (residue O) = 0 := by
      ext i j
      obtain ⟨y, hy⟩ := (hM0 _).1 ((hA 0 _).2 ⟨Pi.single j 1, rfl⟩)
      have hij : A 0 i j = ϖ * y i := by
        have h1 := congrFun hy i
        simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h1
      have hr : residue O ϖ = 0 :=
        (IsLocalRing.residue_eq_zero_iff ϖ).2 ((IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit)
      simp [hij, hr]
    simp [hz]
  · obtain ⟨S, hS⟩ := solve (A (Fin.last R)) (1 : Matrix (Fin n) (Fin n) O) fun j =>
      (hA _ _).1 (by rw [hlast]; trivial)
    exact (rank_of_mul_eq_one ((A (Fin.last R)).map (residue O)) (S.map (residue O))
      (by rw [← Matrix.map_mul, hS, Matrix.map_one _ (map_zero _) (map_one _)])).1

end GlobalTheory.WachChain
end
end
