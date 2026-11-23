module

public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.ExistsIsotypicDecomposition
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.SaturatedLowerSetSpanOfLowerSetTypesSpan
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.StandardPathBasisAnyRing
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.DividedPowerZeroOfGlActionZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.FormalSeriesConditionsB1ToB4
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.JointTypeLatticeSaturated
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.LiePolarizationDerEqZeroOfDisjoint
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.TypeStar
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.DominantOfIsHighestWeightVectorPolynomial
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.IsotypicSumInfStandardWordsOutsideEqBot
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.RenameMulRenameMemSpanProductBasis
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.SubProjectorProductMemStrict

-- Source module: Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissibleExternalProductOfHyps

section

@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.Joints Formalism.MainNotions.LemmaBAlt

theorem externalProduct_index_finite (H : ExternalProductHyps) {N : ℕ} (r K : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) :
    Finite (PIdx r K LL B) := by
  have := standardPath_index_finite N (r + K) LL B
  refine LinearIndependent.finite_of_le_span_finite _ (H.p16 ℚ N r K LL B).1 (Set.range (wd LL B ℚ)) ?_
  rw [span_words_eq_polynomials, ← (H.p16 ℚ N r K LL B).2]
  exact Submodule.subset_span

theorem span_inf_iSup_externalProduct (D : Formalism.BasicNotions.D7) (H : ExternalProductHyps) (F : Type) [Field F] [CharZero F] {N : ℕ} (r K : ℕ)
    (LL : Letters (Fin N)) (B : Fin N → ℕ) (pi' : Fin (N + 1) → Set (Fin r → ℤ))
    (pi'' : Fin (N + 1) → Set (Fin K → ℤ)) (h' : ∀ i, DomLowerSet (pi' i)) (h'' : ∀ i, DomLowerSet (pi'' i)) :
    Submodule.span F (Set.range (pvec F r K LL B)) ⊓
        (⨆ q ∈ {q : (Fin (N + 1) → Fin r → ℤ) × (Fin (N + 1) → Fin K → ℤ) | ∀ i, q.1 i ∈ pi' i ∧ q.2 i ∈ pi'' i},
          jointType F LL q.1 q.2) =
      Submodule.span F (pvec F r K LL B '' {x | ∀ i, x.1.1.1 i ∈ pi' i ∧ x.1.2.1 i ∈ pi'' i}) := by
  have := externalProduct_index_finite H r K LL B
  let pi : ∀ s, Set (GLWeightLabels N r K s) := fun s => match s with
    | .inl i => pi' i
    | .inr i => pi'' i
  have key := H.sum F _ (Fin (N + 1) ⊕ Fin (N + 1)) (GLWeightLabels N r K) (PIdx r K LL B) (externalProductJointData D H r K LL B) pi
    (fun s => match s with
      | .inl i => (h' i).1
      | .inr i => (h'' i).1)
    (fun s => match s with
      | .inl i => (h' i).2
      | .inr i => (h'' i).2)
  have hsup : (⨆ q ∈ {q : ∀ s, GLWeightLabels N r K s | ∀ s, q s ∈ pi s}, ⨅ s, (externalProductJointData (F := F) D H r K LL B).W s (q s)) =
      ⨆ q ∈ {q : (Fin (N + 1) → Fin r → ℤ) × (Fin (N + 1) → Fin K → ℤ) | ∀ i, q.1 i ∈ pi' i ∧ q.2 i ∈ pi'' i},
          jointType F LL q.1 q.2 := by
    apply le_antisymm
    · refine iSup₂_le fun q hq => ?_
      refine le_iSup₂_of_le (f := fun (q : (Fin (N + 1) → Fin r → ℤ) × (Fin (N + 1) → Fin K → ℤ))
          (_ : q ∈ {q : (Fin (N + 1) → Fin r → ℤ) × (Fin (N + 1) → Fin K → ℤ) |
            ∀ i, q.1 i ∈ pi' i ∧ q.2 i ∈ pi'' i}) => jointType F LL q.1 q.2)
        (fun i => q (.inl i), fun i => q (.inr i)) (fun i => ⟨hq (.inl i), hq (.inr i)⟩) ?_
      exact le_iInf fun i => le_inf (iInf_le (fun s => (externalProductJointData (F := F) D H r K LL B).W s (q s)) (Sum.inl i))
        (iInf_le (fun s => (externalProductJointData (F := F) D H r K LL B).W s (q s)) (Sum.inr i))
    · refine iSup₂_le fun q hq => ?_
      refine le_iSup₂_of_le (f := fun (q : ∀ s, GLWeightLabels N r K s) (_ : q ∈ {q : ∀ s, GLWeightLabels N r K s | ∀ s, q s ∈ pi s}) =>
          ⨅ s, (externalProductJointData (F := F) D H r K LL B).W s (q s))
        (fun s => match s with
          | .inl i => q.1 i
          | .inr i => q.2 i)
        (fun s => match s with
          | .inl i => (hq i).1
          | .inr i => (hq i).2) ?_
      exact le_iInf fun s => match s with
        | .inl i => (iInf_le _ i).trans inf_le_left
        | .inr i => (iInf_le _ i).trans inf_le_right
  have hset : {x | ∀ s, (externalProductJointData (F := F) D H r K LL B).P x s ∈ pi s} =
      {x : PIdx r K LL B | ∀ i, x.1.1.1 i ∈ pi' i ∧ x.1.2.1 i ∈ pi'' i} := by
    ext x
    constructor
    · intro h i
      exact ⟨h (.inl i), h (.inr i)⟩
    · intro h s
      match s with
      | .inl i => exact (h i).1
      | .inr i => exact (h i).2
  rw [(H.p16 F N r K LL B).2, ← hsup, ← hset]
  exact key

theorem map_externalProduct_vector {O Kf : Type} [CommRing O] [CommRing Kf] (φ : O →+* Kf) {N : ℕ} (r K : ℕ) (LL : Letters (Fin N))
    (B : Fin N → ℕ) (x : PIdx r K LL B) : MvPolynomial.map φ (pvec O r K LL B x) = pvec Kf r K LL B x := by
  unfold pvec PsiPl PsiTan
  rw [map_mul, MvPolynomial.map_rename, MvPolynomial.map_rename, map_Psi', map_Psi']

theorem admissible_externalProduct_of_hyps (D : Formalism.BasicNotions.D7) (H : ExternalProductHyps) : PairedPathIndependence D := by
  intro O _ _ _ _ N r K _ _ LL B
  have hP := H.p16 O N r K LL B
  refine ⟨⟨hP.1, ?_⟩, ?_⟩
  · rw [← hP.2]
    congr 1
    ext G
    constructor
    · rintro ⟨nu, ka, I', I'', h1, h2, h3, rfl⟩
      exact ⟨⟨((nu, I'), (ka, I'')), h1, h2, h3⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x.1.1.1, x.1.2.1, x.1.1.2, x.1.2.2, x.2.1, x.2.2.1, x.2.2.2, rfl⟩
  · intro pi' pi'' h' h''
    have hint := span_inter_eq_span_image (IsFractionRing.injective O (KK O)) (pvec O r K LL B) (pvec (KK O) r K LL B)
      (map_externalProduct_vector (algebraMap O (KK O)) r K LL B) (H.p16 (KK O) N r K LL B).1 _ _
      (span_inf_iSup_externalProduct D H (KK O) r K LL B pi' pi'' h' h'')
    rw [hP.2] at hint
    rw [hint]
    congr 2
    ext G
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.1.1.1, x.1.2.1, x.1.1.2, x.1.2.2, x.2.1, hx, x.2.2.1, x.2.2.2, rfl⟩
    · rintro ⟨nu, ka, I', I'', h1, hx, h2, h3, rfl⟩
      exact ⟨⟨((nu, I'), (ka, I'')), h1, h2, h3⟩, hx, rfl⟩

end Formalism.MainNotions.G.ColumnFamilies
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.DisjointRestrictSupportOfDisjoint

section

@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.LemmaBAlt

theorem disjoint_restrictSupport_of_disjoint {R σ : Type*} [CommRing R] {s t : Set (σ →₀ ℕ)} (h : Disjoint s t) :
    Disjoint (MvPolynomial.restrictSupport R s) (MvPolynomial.restrictSupport R t) := by
  rw [Submodule.disjoint_def]
  intro x hs ht
  rw [MvPolynomial.mem_restrictSupport_iff] at hs ht
  by_contra hx
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.2 hx
  exact (Set.disjoint_left.1 h) (hs (by simpa using hm)) (ht (by simpa using hm))

theorem linearIndependent_words_all_degrees (R : Type) [CommRing R] (N n : ℕ) (LL : Letters (Fin N)) :
    LinearIndependent R (fun x : (Σ b : Fin N → ℕ, WI n N LL b) => Psi R x.2.1.1.mu x.2.1.2) := by
  refine linearIndependent_iUnion_finite (f := fun (b : Fin N → ℕ) (x : WI n N LL b) => Psi R x.1.1.mu x.1.2)
    (fun b => (standardPath_basis_any_ring R N n LL b).1) ?_
  intro b t _ hb
  have h1 : ∀ b' : Fin N → ℕ, Submodule.span R (Set.range fun x : WI n N LL b' => Psi R x.1.1.mu x.1.2) ≤
      Pol R n b' := by
    intro b'
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact standardWord_mem_multihomogeneous R x.1.1 x.1.2 x.2
  have h2 : (⨆ i ∈ t, Submodule.span R (Set.range fun x : WI n N LL i => Psi R x.1.1.mu x.1.2)) ≤
      MvPolynomial.restrictSupport R {m : Fin N × Fin n →₀ ℕ | ∃ i ∈ t, ∀ j, multideg m j = i j} := by
    refine iSup₂_le fun i hi => (h1 i).trans ?_
    intro x hx
    rw [Pol, MvPolynomial.mem_restrictSupport_iff] at hx
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro m hm
    exact ⟨i, hi, hx hm⟩
  refine Disjoint.mono (h1 b) h2 (disjoint_restrictSupport_of_disjoint ?_)
  rw [Set.disjoint_left]
  rintro m hm ⟨i, hi, hmi⟩
  apply hb
  have : b = i := by
    funext j
    rw [← hm j, hmi j]
  rw [this]
  exact hi

section Theta

variable (R : Type) [CommRing R] (N r K : ℕ)

def towerToPolynomialHom : MvPolynomial (Fin N × Fin r) (MvPolynomial (Fin N × Fin K) R) →+*
    MvPolynomial (Fin N × Fin (r + K)) R :=
  MvPolynomial.eval₂Hom (rename (tanVar (r := r)) : MvPolynomial (Fin N × Fin K) R →ₐ[R] _).toRingHom
    (fun v => X (plVar (K := K) v))

def joinVarsRingHom : MvPolynomial (Fin N × Fin (r + K)) R →+*
    MvPolynomial (Fin N × Fin r) (MvPolynomial (Fin N × Fin K) R) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C)
    (fun v => Fin.addCases (motive := fun _ => MvPolynomial (Fin N × Fin r) (MvPolynomial (Fin N × Fin K) R))
      (fun a => X (v.1, a)) (fun b => C (X (v.1, b))) v.2)

theorem towerToPolynomialHom_C_eq_rename_tan (s : MvPolynomial (Fin N × Fin K) R) : towerToPolynomialHom R N r K (C s) = rename (tanVar (r := r)) s := by
  simp [towerToPolynomialHom]

theorem towerToPolynomialHom_X_eq_X_pl (v : Fin N × Fin r) : towerToPolynomialHom R N r K (X v) = X (plVar (K := K) v) := by
  simp [towerToPolynomialHom]

theorem joinVarsRingHom_comp_towerToPolynomialHom_eq_id : (joinVarsRingHom R N r K).comp (towerToPolynomialHom R N r K) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro s
    have : ((joinVarsRingHom R N r K).comp (towerToPolynomialHom R N r K)).comp MvPolynomial.C = (RingHom.id _).comp MvPolynomial.C := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp [towerToPolynomialHom_C_eq_rename_tan, joinVarsRingHom]
      · intro w
        simp [towerToPolynomialHom_C_eq_rename_tan, joinVarsRingHom, tanVar]
    exact congrArg (fun f => f s) this
  · intro v
    simp [towerToPolynomialHom_X_eq_X_pl, joinVarsRingHom, plVar]

theorem towerToPolynomialHom_injective : Function.Injective (towerToPolynomialHom R N r K) := by
  intro x y h
  have := congrArg (joinVarsRingHom R N r K) h
  have e : ∀ z, joinVarsRingHom R N r K (towerToPolynomialHom R N r K z) = z := fun z => congrArg (fun f => f z) (joinVarsRingHom_comp_towerToPolynomialHom_eq_id R N r K)
  rwa [e, e] at this

theorem towerToPolynomialHom_map_C_eq_rename_pl (a : MvPolynomial (Fin N × Fin r) R) :
    towerToPolynomialHom R N r K (MvPolynomial.map MvPolynomial.C a) = rename (plVar (K := K)) a := by
  have : (towerToPolynomialHom R N r K).comp (MvPolynomial.map MvPolynomial.C) =
      (rename (plVar (K := K)) : MvPolynomial (Fin N × Fin r) R →ₐ[R] _).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [towerToPolynomialHom_C_eq_rename_tan]
    · intro v
      simp [towerToPolynomialHom_X_eq_X_pl]
  exact congrArg (fun f => f a) this

def towerToPolynomialLinearMap : MvPolynomial (Fin N × Fin r) (MvPolynomial (Fin N × Fin K) R) →ₗ[R]
    MvPolynomial (Fin N × Fin (r + K)) R where
  toFun := towerToPolynomialHom R N r K
  map_add' := map_add _
  map_smul' := by
    intro c x
    have h1 : c • x = C (C c) * x := by
      rw [← MvPolynomial.smul_eq_C_mul, ← MvPolynomial.algebraMap_eq, algebraMap_smul]
    rw [h1, map_mul, towerToPolynomialHom_C_eq_rename_tan, rename_C, RingHom.id_apply, MvPolynomial.smul_eq_C_mul]

end Theta

theorem linearIndependent_productBasis (R : Type) [CommRing R] (N r K : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) :
    LinearIndependent R (pvec R r K LL B) := by
  classical
  have hb := linearIndependent_words_all_degrees R N K LL
  have hc := linearIndependent_words_all_degrees (MvPolynomial (Fin N × Fin K) R) N r LL
  have hbc := linearIndependent_smul hb hc
  have hex : ∀ x : PIdx r K LL B, ∃ y : (Σ b : Fin N → ℕ, WI K N LL b) × (Σ b : Fin N → ℕ, WI r N LL b),
      y.1.2.1.1.mu = x.1.2.1 ∧ y.1.2.1.2 = x.1.2.2 ∧ y.2.2.1.1.mu = x.1.1.1 ∧ y.2.2.1.2 = x.1.1.2 := by
    rintro ⟨⟨⟨nu, I'⟩, ⟨ka, I''⟩⟩, ⟨b', b'', _, ⟨P1, e1⟩, ⟨P2, e2⟩⟩, h2, h3⟩
    have e1' : P1.mu = nu := e1
    have e2' : P2.mu = ka := e2
    have h2' : IsSt P1.mu I' := by rw [e1']; exact h2
    have h3' : IsSt P2.mu I'' := by rw [e2']; exact h3
    exact ⟨(⟨b'', ⟨(P2, I''), h3'⟩⟩, ⟨b', ⟨(P1, I'), h2'⟩⟩), e2', rfl, e1', rfl⟩
  choose io hio using hex
  have hinj : Function.Injective io := by
    intro x y hxy
    obtain ⟨a1, a2, a3, a4⟩ := hio x
    obtain ⟨c1, c2, c3, c4⟩ := hio y
    rw [hxy] at a1 a2 a3 a4
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · rw [← a3, c3]
      · rw [← a4, c4]
    · apply Prod.ext
      · rw [← a1, c1]
      · rw [← a2, c2]
  have h1 := (hbc.comp io hinj).map' (towerToPolynomialLinearMap R N r K)
    (LinearMap.ker_eq_bot.2 (towerToPolynomialHom_injective R N r K))
  have h2 : (⇑(towerToPolynomialLinearMap R N r K) ∘ (fun p : (Σ b : Fin N → ℕ, WI K N LL b) × (Σ b : Fin N → ℕ, WI r N LL b) =>
      Psi R p.1.2.1.1.mu p.1.2.1.2 • Psi (MvPolynomial (Fin N × Fin K) R) p.2.2.1.1.mu p.2.2.1.2) ∘ io) =
      pvec R r K LL B := by
    funext x
    obtain ⟨a1, a2, a3, a4⟩ := hio x
    simp only [Function.comp_apply]
    rw [a1, a2, a3, a4]
    change towerToPolynomialHom R N r K _ = _
    rw [MvPolynomial.smul_eq_C_mul, map_mul, towerToPolynomialHom_C_eq_rename_tan, ← map_Psi' (MvPolynomial.C : R →+* _), towerToPolynomialHom_map_C_eq_rename_pl]
    unfold pvec PsiPl PsiTan
    rw [mul_comm]
  rw [← h2]
  exact h1

end Formalism.MainNotions.G.ColumnFamilies
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissibleExternalProduct

section

@[expose] public section

namespace Formalism.MainNotions.G.ColumnFamilies

theorem externalProduct_basis : ExternalProductBasis := fun R _ N r K LL B => ⟨linearIndependent_productBasis R N r K LL B, span_productBasis_eq_multihomogeneous R N r K LL B⟩

theorem externalProductHyps (D : Formalism.BasicNotions.D7) : ExternalProductHyps := {
  p16 := externalProduct_basis
  e1 := determinant_divisibility
  e2 := polynomialHighestWeight_dominant D
  e3 := projectors_preserve_multidegree
  e5a := polynomialProjectors_commute_nested
  e5b := polynomialProjectors_commute_disjoint
  lowPl := restLowPl_of D (polynomialTypeSums_by_evaluation D) externalProduct_basis
  lowTan := restLowTan_of D (polynomialTypeSums_by_evaluation D) externalProduct_basis
  sum := restJointSum }

theorem admissible_externalProduct (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.PairedPathIndependence D := admissible_externalProduct_of_hyps D (externalProductHyps D)

end Formalism.MainNotions.G.ColumnFamilies
end
end
