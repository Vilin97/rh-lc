module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameLatticeTraceInitialSpanVolumeEq
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
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualInterSelfDualHermitianLatticeSubspace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexSpanLatticeMatrixDetNorm
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBoundStatement
import Mathlib.Tactic.TypeStar

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameLatticeTraceInitialSpanVolumeEqStatement

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.frameLattice_trace_initialSpan_volume_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ d' Λ', S.IsTerm d' Λ' → ∀ (J : ℕ) (Yy : Submodule L.O S.V), J ≤ r + 1 → Yy = (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O → (S.M d Λ ⊓ Yy).toAddSubgroup.relIndex (S.M d' Λ' ⊓ Yy).toAddSubgroup = (S.M d' Λ' ⊓ Yy).toAddSubgroup.relIndex (S.M d Λ ⊓ Yy).toAddSubgroup ∧ (S.M d Λ ⊓ Yy).toAddSubgroup.relIndex (S.M d' Λ' ⊓ Yy).toAddSubgroup ≠ 0 := by
  first | exact @GlobalTheory.HL.TraceVol.trace_volume | exact GlobalTheory.HL.TraceVol.trace_volume | (intros; apply GlobalTheory.HL.TraceVol.trace_volume <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexSpanLatticeMatrixDetNormStatement

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.relIndex_span_lattice_matrix_det_norm : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ {n m : ℕ} (b : Fin m → Fin n → E), LinearIndependent E b → ∀ (A : Matrix (Fin m) (Fin m) E) (c : F), c ≠ 0 → A.det * L.cj A.det = algebraMap F E c → ∀ Q Q' : Submodule L.O (Fin n → E), Q = Submodule.span L.O (Set.range b) → Q' = Submodule.span L.O (Set.range fun j => ∑ i, A i j • b i) → Q'.toAddSubgroup.relIndex Q.toAddSubgroup ≠ 0 ∧ Q.toAddSubgroup.relIndex Q'.toAddSubgroup ≠ 0 ∧ (Q'.toAddSubgroup.relIndex Q.toAddSubgroup : ℝ) = (resQ ϖ : ℝ) ^ (vE L ϖ (algebraMap F E c)) * (Q.toAddSubgroup.relIndex Q'.toAddSubgroup : ℝ) := by
  first | exact @GlobalTheory.HL.FrameIndex.relIndex_span_matrix | exact GlobalTheory.HL.FrameIndex.relIndex_span_matrix | (intros; apply GlobalTheory.HL.FrameIndex.relIndex_span_matrix <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualHermitianLatticeTraceOrthogonalVolumeRat

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.VolPerp

open GlobalTheory.HL.DualInter

theorem relIndex_split {G : Type} [AddCommGroup G] {M A : AddSubgroup G} (Z : AddSubgroup G)
    (h : M ≤ A) : M.relIndex A = (M ⊓ Z).relIndex (A ⊓ Z) * (M ⊔ Z).relIndex (A ⊔ Z) := by
  have h1 : (M ⊔ Z) ⊓ A = M ⊔ (Z ⊓ A) := sup_inf_assoc_of_le Z h
  have h2 : M ≤ (M ⊔ Z) ⊓ A := le_inf le_sup_left h
  rw [← AddSubgroup.relIndex_mul_relIndex M _ A h2 inf_le_right]
  congr 1
  · rw [h1, AddSubgroup.relIndex_sup_left, ← AddSubgroup.inf_relIndex_right M, inf_comm Z A,
      ← inf_assoc, inf_eq_left.2 h]
  · rw [AddSubgroup.inf_relIndex_right, ← AddSubgroup.relIndex_sup_right A (M ⊔ Z),
      ← sup_assoc, sup_eq_left.2 h]

theorem relIndex_split' {G : Type} [AddCommGroup G] (A B Z : AddSubgroup G) :
    B.relIndex A = (B ⊓ Z).relIndex (A ⊓ Z) *
      (((A ⊓ B) ⊔ Z).relIndex ((A ⊔ Z) ⊓ (B ⊔ Z)) * (B ⊔ Z).relIndex (A ⊔ Z)) := by
  rw [← AddSubgroup.inf_relIndex_left, relIndex_split Z inf_le_left]
  congr 1
  · rw [inf_inf_distrib_right, AddSubgroup.inf_relIndex_left]
  · rw [← AddSubgroup.inf_relIndex_left (A ⊔ Z) (B ⊔ Z), AddSubgroup.relIndex_mul_relIndex _ _ _
      (le_inf (sup_le_sup_right inf_le_left _) (sup_le_sup_right inf_le_right _)) inf_le_left]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}

theorem expand {m : ℕ} {b c : Fin m → Fin n → E}
    (hbc : ∀ i j, hf L Hm (b i) (c j) = if i = j then 1 else 0) {v : Fin n → E}
    (hv : v ∈ Submodule.span E (Set.range b)) : v = ∑ j, hf L Hm v (c j) • b j := by
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hv
  simp [sum_l, smul_l, hbc]

theorem inter_eq {Λ : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ) {m : ℕ}
    {b c : Fin m → Fin n → E} (hb : ∀ i, b i ∈ Λ) (hc : ∀ i, c i ∈ Λ)
    (hbc : ∀ i j, hf L Hm (b i) (c j) = if i = j then 1 else 0) :
    Λ ⊓ (Submodule.span E (Set.range b)).restrictScalars L.O
      = Submodule.span L.O (Set.range b) := by
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rintro v ⟨hv, hvY⟩
    rw [expand hbc hvY]
    refine Submodule.sum_mem _ fun j _ => ?_
    exact Submodule.smul_mem (Submodule.span L.O (Set.range b))
      ⟨_, (hΛ.2 _).2 (hc j) _ hv⟩ (Submodule.subset_span ⟨j, rfl⟩)
  · rintro _ ⟨j, rfl⟩
    exact ⟨hb j, Submodule.subset_span ⟨j, rfl⟩⟩

theorem map_eq (h : IsHermND L Hm) {Λ : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ) {m : ℕ}
    {b c : Fin m → Fin n → E} (hb : ∀ i, b i ∈ Λ) (hc : ∀ i, c i ∈ Λ)
    (hbc : ∀ i j, hf L Hm (b i) (c j) = if i = j then 1 else 0)
    (φ : (Fin n → E) →ₗ[E] (Fin m → E)) (w : Fin m → Fin m → E)
    (hφ : ∀ v, φ v = ∑ j, hf L Hm v (b j) • w j) :
    Λ.toAddSubgroup.map φ.toAddMonoidHom = (Submodule.span L.O (Set.range w)).toAddSubgroup := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    change φ v ∈ Submodule.span L.O (Set.range w)
    rw [hφ]
    refine Submodule.sum_mem _ fun j _ => ?_
    exact Submodule.smul_mem (Submodule.span L.O (Set.range w))
      ⟨_, (hΛ.2 _).2 (hb j) _ hv⟩ (Submodule.subset_span ⟨j, rfl⟩)
  · intro hx
    have : Submodule.span L.O (Set.range w) ≤ Λ.map (φ.restrictScalars L.O) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      refine ⟨c j, hc j, ?_⟩
      have : ∀ i, hf L Hm (c j) (b i) = if i = j then 1 else 0 := fun i => by
        rw [← cj_hf h, hbc]; split_ifs <;> simp
      simp [hφ, this]
    exact this hx

theorem key (h : IsHermND L Hm) {Λ Λ' : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ)
    (hΛ' : IsSD L Hm Λ') {m : ℕ} (y : Fin m → Fin n → E) (hy : LinearIndependent E y)
    {Y Z : Submodule L.O (Fin n → E)}
    (hY : Y = (Submodule.span E (Set.range y)).restrictScalars L.O)
    (hZ : Z = (perp L Hm (Submodule.span E (Set.range y))).restrictScalars L.O) :
    (Λ ⊓ Y).toAddSubgroup.relIndex (Λ' ⊓ Y).toAddSubgroup ≠ 0 ∧
    (Λ.toAddSubgroup ⊔ Z.toAddSubgroup).relIndex (Λ'.toAddSubgroup ⊔ Z.toAddSubgroup) *
      (Λ ⊓ Y).toAddSubgroup.relIndex (Λ' ⊓ Y).toAddSubgroup =
    (Λ'.toAddSubgroup ⊔ Z.toAddSubgroup).relIndex (Λ.toAddSubgroup ⊔ Z.toAddSubgroup) *
      (Λ' ⊓ Y).toAddSubgroup.relIndex (Λ ⊓ Y).toAddSubgroup := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have := L.free
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; omega)
  obtain ⟨b, c, hb, hc, hs, hbc⟩ := exists_dual_family h hΛ m y hy
  obtain ⟨b', c', hb', hc', hs', hbc'⟩ := exists_dual_family h hΛ' m y hy
  have hQ : Λ ⊓ Y = Submodule.span L.O (Set.range b) := by
    rw [hY, ← hs]; exact inter_eq hΛ hb hc hbc
  have hQ' : Λ' ⊓ Y = Submodule.span L.O (Set.range b') := by
    rw [hY, ← hs']; exact inter_eq hΛ' hb' hc' hbc'
  let A : Matrix (Fin m) (Fin m) E := fun i j => hf L Hm (b' j) (c i)
  let B : Matrix (Fin m) (Fin m) E := fun i j => hf L Hm (b j) (c' i)
  have hA : ∀ j, b' j = ∑ i, A i j • b i := fun j =>
    expand hbc (by rw [hs, ← hs']; exact Submodule.subset_span ⟨j, rfl⟩)
  have hBA : B * A = 1 := by
    ext k j
    have := hbc' j k
    rw [hA j, sum_l] at this
    simp only [smul_l] at this
    rw [Matrix.mul_apply, Matrix.one_apply, ← if_congr eq_comm rfl rfl, ← this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hu : IsUnit A.det := Matrix.isUnit_det_of_left_inverse hBA
  obtain ⟨d, hd⟩ := (L.cj_fix (A.det * L.cj A.det)).1 (by rw [map_mul, L.cj_cj, mul_comm])
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact (hu.mul (hu.map L.cj)).ne_zero (by rw [← hd, map_zero])
  have hli : LinearIndependent E b := by
    refine Fintype.linearIndependent_iff.2 fun g hg k => ?_
    have := congrArg (fun v => hf L Hm v (c k)) hg
    simp only [sum_l, smul_l, hbc] at this
    simpa [hf] using this
  obtain ⟨-, p2, p3⟩ := GlobalTheory.T.relIndex_span_lattice_matrix_det_norm L ϖ hϖ b hli A d hd0 hd.symm (Λ ⊓ Y) (Λ' ⊓ Y) hQ
    (by rw [hQ']; congr 2; exact funext hA)
  have hdet : (cT L A).det = L.cj A.det := by
    have : cT L A = ((L.cj : E →+* E).mapMatrix A).transpose := rfl
    rw [this, Matrix.det_transpose, ← RingHom.map_det]; rfl
  obtain ⟨-, -, r3⟩ := GlobalTheory.T.relIndex_span_lattice_matrix_det_norm L ϖ hϖ (Pi.basisFun E (Fin m))
    (Pi.basisFun E (Fin m)).linearIndependent (cT L A) d hd0
    (by rw [hdet, L.cj_cj, mul_comm, hd]) _ _ rfl rfl
  let φ : (Fin n → E) →ₗ[E] (Fin m → E) := LinearMap.pi fun j => hfL L Hm (b' j)
  have hφ : ∀ v k, φ v k = hf L Hm v (b' k) := fun v k => rfl
  have m1 := map_eq h hΛ' hb' hc' hbc' φ (Pi.basisFun E (Fin m))
    (fun v => by ext k; simp [hφ, Pi.single_apply])
  have m2 := map_eq h hΛ hb hc hbc φ (fun j => ∑ i, cT L A i j • Pi.basisFun E (Fin m) i)
    (fun v => by
      ext k
      rw [hφ, hA k]
      simp [sum_r, smul_r, cT, Pi.single_apply, mul_comm])
  rw [← m1, ← m2, AddSubgroup.relIndex_map_map, AddSubgroup.relIndex_map_map] at r3
  have hker : φ.toAddMonoidHom.ker = Z.toAddSubgroup := by
    ext x
    rw [hZ, ← hs']
    constructor
    · intro hx v hv
      rw [← cj_hf h, hf_eq_zero_of_span (S := Set.range b') ?_ v hv, map_zero]
      rintro _ ⟨j, rfl⟩
      have : hf L Hm x (b' j) = 0 := congrFun hx j
      rw [← cj_hf h, this, map_zero]
    · intro hx
      funext j
      exact hx _ (Submodule.subset_span ⟨j, rfl⟩)
  rw [hker] at r3
  refine ⟨p2, ?_⟩
  apply Nat.cast_injective (R := ℝ)
  push_cast
  rw [p3, r3]
  ring

theorem relIndex_symm (h : IsHermND L Hm) {Λ Λ' : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ)
    (hΛ' : IsSD L Hm Λ') : Λ.toAddSubgroup.relIndex Λ'.toAddSubgroup ≠ 0 ∧
    Λ.toAddSubgroup.relIndex Λ'.toAddSubgroup = Λ'.toAddSubgroup.relIndex Λ.toAddSubgroup := by
  have hY : (⊤ : Submodule L.O (Fin n → E))
      = (Submodule.span E (Set.range (Pi.basisFun E (Fin n)))).restrictScalars L.O := by
    rw [Module.Basis.span_eq]; rfl
  have hZ : (⊥ : Submodule L.O (Fin n → E))
      = (perp L Hm (Submodule.span E (Set.range (Pi.basisFun E (Fin n))))).restrictScalars L.O := by
    rw [Module.Basis.span_eq, eq_comm, eq_bot_iff]
    intro x hx
    refine eq_zero_of_hf h fun v => ?_
    rw [← cj_hf h, hx v trivial, map_zero]
  obtain ⟨k1, k2⟩ := key h hΛ hΛ' _ (Pi.basisFun E (Fin n)).linearIndependent hY hZ
  simp only [inf_top_eq, Submodule.bot_toAddSubgroup, sup_bot_eq] at k1 k2
  exact ⟨k1, Nat.mul_self_inj.1 k2⟩

theorem vol_perp : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ Λ', IsSD L Hm Λ → IsSD L Hm Λ' → ∀ (m : ℕ) (y : Fin m → Fin n → E), LinearIndependent E y → ∀ Y Z : Submodule L.O (Fin n → E), Y = (Submodule.span E (Set.range y)).restrictScalars L.O → Z = (perp L Hm (Submodule.span E (Set.range y))).restrictScalars L.O → (Λ ⊓ Z).toAddSubgroup.relIndex (Λ' ⊓ Z).toAddSubgroup ≠ 0 ∧ (Λ ⊓ Y).toAddSubgroup.relIndex (Λ' ⊓ Y).toAddSubgroup ≠ 0 ∧ (Λ ⊓ Z).toAddSubgroup.relIndex (Λ' ⊓ Z).toAddSubgroup * (Λ' ⊓ Y).toAddSubgroup.relIndex (Λ ⊓ Y).toAddSubgroup = (Λ' ⊓ Z).toAddSubgroup.relIndex (Λ ⊓ Z).toAddSubgroup * (Λ ⊓ Y).toAddSubgroup.relIndex (Λ' ⊓ Y).toAddSubgroup := by
  intro F _ _ _ _ _ E _ _ _ L n Hm h Λ Λ' hΛ hΛ' m y hy Y Z hY hZ
  obtain ⟨k1, k2⟩ := key h hΛ hΛ' y hy hY hZ
  obtain ⟨a1, a2⟩ := relIndex_symm h hΛ hΛ'
  have s1 := relIndex_split' Λ.toAddSubgroup Λ'.toAddSubgroup Z.toAddSubgroup
  have s2 := relIndex_split' Λ'.toAddSubgroup Λ.toAddSubgroup Z.toAddSubgroup
  rw [inf_comm Λ'.toAddSubgroup Λ.toAddSubgroup, inf_comm (Λ'.toAddSubgroup ⊔ _)] at s2
  have e1 : (Λ ⊓ Z).toAddSubgroup = Λ.toAddSubgroup ⊓ Z.toAddSubgroup := rfl
  have e2 : (Λ' ⊓ Z).toAddSubgroup = Λ'.toAddSubgroup ⊓ Z.toAddSubgroup := rfl
  rw [e1, e2]
  have b1 := a2 ▸ a1
  rw [s1] at b1
  rw [s1, s2] at a2
  rw [s2] at a1
  simp only [ne_eq, mul_eq_zero, not_or] at a1 b1
  refine ⟨a1.1, k1, ?_⟩
  rw [mul_left_comm, mul_left_comm _ (AddSubgroup.relIndex (_ ⊓ _ ⊔ _) _)] at a2
  have a3 := mul_left_cancel₀ a1.2.1 a2
  refine mul_right_cancel₀ b1.2.2 ?_
  rw [mul_assoc, mul_comm (AddSubgroup.relIndex (Λ' ⊓ Y).toAddSubgroup _), ← k2, ← mul_assoc, a3]
  ring

end GlobalTheory.HL.VolPerp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualHermitianLatticeTraceOrthogonalVolumeRatStatement

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.selfDualHermitianLattice_trace_orthogonal_volume_ratio : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ Λ', IsSD L Hm Λ → IsSD L Hm Λ' → ∀ (m : ℕ) (y : Fin m → Fin n → E), LinearIndependent E y → ∀ Y Z : Submodule L.O (Fin n → E), Y = (Submodule.span E (Set.range y)).restrictScalars L.O → Z = (perp L Hm (Submodule.span E (Set.range y))).restrictScalars L.O → (Λ ⊓ Z).toAddSubgroup.relIndex (Λ' ⊓ Z).toAddSubgroup ≠ 0 ∧ (Λ ⊓ Y).toAddSubgroup.relIndex (Λ' ⊓ Y).toAddSubgroup ≠ 0 ∧ (Λ ⊓ Z).toAddSubgroup.relIndex (Λ' ⊓ Z).toAddSubgroup * (Λ' ⊓ Y).toAddSubgroup.relIndex (Λ ⊓ Y).toAddSubgroup = (Λ' ⊓ Z).toAddSubgroup.relIndex (Λ ⊓ Z).toAddSubgroup * (Λ ⊓ Y).toAddSubgroup.relIndex (Λ' ⊓ Y).toAddSubgroup := by
  first | exact @GlobalTheory.HL.VolPerp.vol_perp | exact GlobalTheory.HL.VolPerp.vol_perp | (intros; apply GlobalTheory.HL.VolPerp.vol_perp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFamilyTraceVolumeConst

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FamilyVol

theorem relIndex_symm_of_sub {G : Type*} [AddGroup G] {A A' B B' : AddSubgroup G} {β : ℕ} (hβ : β ≠ 0)
    (hA : B ≤ A) (hA' : B' ≤ A') (h : B.relIndex A = β) (h' : B'.relIndex A' = β)
    (hB : B.relIndex B' = B'.relIndex B) (hB0 : B.relIndex B' ≠ 0) :
    A.relIndex A' = A'.relIndex A := by
  have e1 : (B ⊓ B').relIndex A = B'.relIndex B * β := by
    rw [← h, ← AddSubgroup.relIndex_mul_relIndex (B ⊓ B') B A inf_le_left hA,
      AddSubgroup.inf_relIndex_left]
  have e2 : (B ⊓ B').relIndex A' = B.relIndex B' * β := by
    rw [← h', ← AddSubgroup.relIndex_mul_relIndex (B ⊓ B') B' A' inf_le_right hA',
      AddSubgroup.inf_relIndex_right]
  have hle : B ⊓ B' ≤ A ⊓ A' := inf_le_inf hA hA'
  have e3 := AddSubgroup.relIndex_mul_relIndex (B ⊓ B') (A ⊓ A') A hle inf_le_left
  have e4 := AddSubgroup.relIndex_mul_relIndex (B ⊓ B') (A ⊓ A') A' hle inf_le_right
  rw [AddSubgroup.inf_relIndex_left] at e3
  rw [AddSubgroup.inf_relIndex_right] at e4
  have hne : (B ⊓ B').relIndex (A ⊓ A') ≠ 0 := by
    intro h0
    rw [h0, zero_mul, e2] at e4
    exact mul_ne_zero hB0 hβ e4.symm
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne)
  rw [e3, e4, e1, e2, hB]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem resQ_ne_zero (ϖ : 𝒪[F]) (h : Irreducible ϖ) : resQ ϖ ≠ 0 := by
  have e : Ideal.span {ϖ} = IsLocalRing.maximalIdeal 𝒪[F] := h.maximalIdeal_eq.symm
  unfold resQ
  rw [e]
  have : Finite (𝒪[F] ⧸ IsLocalRing.maximalIdeal 𝒪[F]) := inferInstanceAs (Finite 𝓀[F])
  exact Nat.card_pos.ne'

variable [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E} {r k : ℕ}

theorem exists_basis (S : Frames L r k) (J : ℕ) :
    ∃ (m : ℕ) (y : Fin m → S.V), LinearIndependent E y ∧
      Submodule.span E (Set.range y) = S.spanTo S.f J ⊔ S.spanTo S.f' J := by
  have hli := (GlobalTheory.FrameBasic.main L r k S).1
  let I := {i : Fin (r + 1) // (i : ℕ) < J}
  let φ : I ⊕ I → Fin (r + 1) ⊕ Fin (r + 1) := Sum.map Subtype.val Subtype.val
  have hφ : Function.Injective φ := Subtype.val_injective.sumMap Subtype.val_injective
  let e := (Fintype.equivFin (I ⊕ I)).symm
  refine ⟨_, (Sum.elim S.f S.f' ∘ φ) ∘ e, (hli.comp φ hφ).comp e e.injective, ?_⟩
  rw [e.surjective.range_comp, Frames.spanTo, Frames.spanTo, ← Submodule.span_union]
  congr 1
  ext v
  constructor
  · rintro ⟨i | i, rfl⟩
    · exact Or.inl ⟨i.1, i.2, rfl⟩
    · exact Or.inr ⟨i.1, i.2, rfl⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact ⟨Sum.inl ⟨i, hi⟩, rfl⟩
    · exact ⟨Sum.inr ⟨i, hi⟩, rfl⟩

theorem spanTo_mono (S : Frames L r k) (g : Fin (r + 1) → S.V) {i j : ℕ} (h : i ≤ j) :
    S.spanTo g i ≤ S.spanTo g j :=
  Submodule.span_mono (Set.image_mono fun _ ha => lt_of_lt_of_le ha h)

theorem relIndex_trace (S : Frames L r k) (J : ℕ) (hJ : J ≤ r + 1) (d : S.Datum) (Λ : Submodule L.O S.V)
    (hT : S.IsTerm d Λ) (hl : ∀ y ∈ S.sat Λ, S.levC d Λ y ≤ J) :
    (S.M d Λ ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup.relIndex
      (Λ ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup = S.be d Λ := by
  have hM : S.M d Λ ≤ S.sat Λ := (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).2.2.1
  have hlev := (GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ hT).2.2.2.2.2.2.2.2.2.2
  set Y := (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O with hY
  have h1 : (S.sat Λ).toAddSubgroup = (Λ ⊓ Y).toAddSubgroup ⊔ (S.M d Λ).toAddSubgroup := by
    apply le_antisymm
    · intro y hy
      obtain ⟨y₁, hy₁, hm⟩ := (hlev y hy J).1 (hl y hy)
      have hy₁Λ : y₁ ∈ Λ := by
        have := Λ.sub_mem hy.1 (hM hm).1
        simpa using this
      have : y = y₁ + (y - y₁) := by abel
      rw [this]
      exact AddSubgroup.add_mem_sup (S := (Λ ⊓ Y).toAddSubgroup) ⟨hy₁Λ, hy₁⟩ hm
    · refine sup_le ?_ hM
      intro y hy
      exact ⟨hy.1, sup_le_sup (spanTo_mono S S.f hJ) (spanTo_mono S S.f' hJ) hy.2⟩
  have h2 : (S.M d Λ ⊓ Y).toAddSubgroup = (S.M d Λ).toAddSubgroup ⊓ (Λ ⊓ Y).toAddSubgroup := by
    ext y
    exact ⟨fun h => ⟨h.1, (hM h.1).1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  rw [h2, AddSubgroup.inf_relIndex_right, Frames.be, h1, AddSubgroup.relIndex_sup_right]

theorem family_vol : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ Λ', S.IsTerm d Λ' → S.InFF β (j + 1) βJ d Λ' → ∀ Yy : Submodule L.O S.V, (Yy = (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)).restrictScalars L.O ∨ Yy = (perp L S.Hm (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1))).restrictScalars L.O) → (Λ ⊓ Yy).toAddSubgroup.relIndex (Λ' ⊓ Yy).toAddSubgroup = (Λ' ⊓ Yy).toAddSubgroup.relIndex (Λ ⊓ Yy).toAddSubgroup ∧ (Λ ⊓ Yy).toAddSubgroup.relIndex (Λ' ⊓ Yy).toAddSubgroup ≠ 0 ∧ (S.M d Λ ⊓ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)).restrictScalars L.O).toAddSubgroup.relIndex (Λ ⊓ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)).restrictScalars L.O).toAddSubgroup = β := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hF Λ' hT' hF' Yy hYy
  have hJ : (j : ℕ) + 1 ≤ r + 1 := by have := j.2; omega
  have b1 := relIndex_trace S (j + 1) hJ d Λ hT hF.2.2.1
  have b2 := relIndex_trace S (j + 1) hJ d Λ' hT' hF'.2.2.1
  have hβ : β ≠ 0 := by
    obtain ⟨i, -, hi⟩ := (GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ hT).2.2.2.2.2.1
    rw [← hF.2.1, hi]
    exact pow_ne_zero _ (resQ_ne_zero _ S.ϖ_irr)
  rw [hF.2.1] at b1
  rw [hF'.2.1] at b2
  obtain ⟨hS, -, hM, -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  obtain ⟨hS', -, hM', -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ' hT'
  obtain ⟨v1, v2⟩ := GlobalTheory.T.frameLattice_trace_initialSpan_volume_eq L r k S d Λ hT d Λ' hT' (j + 1) _ hJ rfl
  have hY := relIndex_symm_of_sub hβ
    (Submodule.toAddSubgroup_mono (inf_le_inf_right _ (hM.trans inf_le_left)))
    (Submodule.toAddSubgroup_mono (inf_le_inf_right _ (hM'.trans inf_le_left))) b1 b2 v1 v2
  obtain ⟨m, y, hy, hsp⟩ := exists_basis S (j + 1)
  obtain ⟨p1, p2, p3⟩ := GlobalTheory.T.selfDualHermitianLattice_trace_orthogonal_volume_ratio L S.Hm S.herm Λ Λ' hS hS' m y hy _ _ rfl rfl
  rw [hsp] at p1 p2 p3
  rcases hYy with rfl | rfl
  · exact ⟨hY, p2, b1⟩
  · refine ⟨?_, p1, b1⟩
    rw [← hY] at p3
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero p2) p3

end GlobalTheory.HL.FamilyVol
end
end
