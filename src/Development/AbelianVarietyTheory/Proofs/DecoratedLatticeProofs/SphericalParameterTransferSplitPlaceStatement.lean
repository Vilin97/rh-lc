module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryChartsAllFinitePlacesFrameLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeOperatorMoveAcrossInvariantBilinearStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeVacuumHeckeIdentitySplitPlaceChartsStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeEsymmScaledMultisetAddSegment
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeVectorIffInverseDoubleCosets

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralGLCommensuratedDoubleCosetCardInvSymm

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.CosetSymGL

abbrev Cos {G : Type} [Group G] (K : Subgroup G) (g : G) : Type :=
  {c : G ⧸ K // ∃ k ∈ K, c = ((k * g : G) : G ⧸ K)}

theorem card_cos_eq_of_mem {G : Type} [Group G] {K : Subgroup G} {g h a b : G} (ha : a ∈ K) (hb : b ∈ K)
    (e : h = a * g * b) : Nat.card (Cos K h) = Nat.card (Cos K g) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k * a, K.mul_mem hk ha, ?_⟩
    rw [e, ← mul_assoc, ← mul_assoc, QuotientGroup.mk_mul_of_mem _ hb]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k * a⁻¹, K.mul_mem hk (K.inv_mem ha), ?_⟩
    rw [e, show k * a⁻¹ * (a * g * b) = k * g * b by group, QuotientGroup.mk_mul_of_mem _ hb]

def quotEquiv {G : Type} [Group G] (K : Subgroup G) (θ : G ≃* G) (hθ : ∀ x, θ x ∈ K ↔ x ∈ K) : G ⧸ K ≃ G ⧸ K :=
  Quotient.congr θ.toEquiv fun a b => by
    change QuotientGroup.leftRel K a b ↔ QuotientGroup.leftRel K (θ a) (θ b)
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, ← map_inv, ← map_mul, hθ]

theorem quotEquiv_mk {G : Type} [Group G] (K : Subgroup G) (θ : G ≃* G) (hθ : ∀ x, θ x ∈ K ↔ x ∈ K) (x : G) :
    quotEquiv K θ hθ (x : G ⧸ K) = ((θ x : G) : G ⧸ K) := rfl

theorem card_cos_aut {G : Type} [Group G] (K : Subgroup G) (θ : G ≃* G) (hθ : ∀ x, θ x ∈ K ↔ x ∈ K) (g : G) :
    Nat.card (Cos K g) = Nat.card (Cos K (θ g)) := by
  refine Nat.card_congr (Equiv.subtypeEquiv (quotEquiv K θ hθ) fun c => ?_)
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨θ k, (hθ k).2 hk, by rw [quotEquiv_mk, map_mul]⟩
  · rintro ⟨k, hk, e⟩
    refine ⟨θ.symm k, (hθ _).1 (by simpa using hk), (quotEquiv K θ hθ).injective ?_⟩
    rw [e, quotEquiv_mk, map_mul, MulEquiv.apply_symm_apply]

theorem cosetSym_of_aut {G : Type} [Group G] (K : Subgroup G) (θ : G ≃* G) (hθ : ∀ x, θ x ∈ K ↔ x ∈ K)
    (h : ∀ g, ∃ a ∈ K, ∃ b ∈ K, θ g = a * g⁻¹ * b) : CosetSym K := fun g => by
  obtain ⟨a, ha, b, hb, e⟩ := h g
  exact (card_cos_aut K θ hθ g).trans (card_cos_eq_of_mem ha hb e)

end GlobalTheory.ChainOnto.CosetSymGL

namespace GlobalTheory.ChainOnto.CosetSymGL


open GlobalTheory.LFun.ConjPlace in
theorem invT_of_symm {L : Type} [Field L] {n : ℕ} (d : GL (Fin n) L)
    (hd : (d : Matrix (Fin n) (Fin n) L)ᵀ = (d : Matrix (Fin n) (Fin n) L)) : invT (RingEquiv.refl L) n d = d⁻¹ := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [invT_val, RingEquiv.refl_apply, Matrix.coe_units_inv]
  conv_lhs => rw [← hd]
  rw [← Matrix.transpose_nonsing_inv, Matrix.transpose_apply]

open GlobalTheory.LFun.ConjPlace in
theorem invT_mem_iff {L : Type} [Field L] {n : ℕ} (O : Subring L) (g : GL (Fin n) L) :
    invT (RingEquiv.refl L) n g ∈ Formalism.UG.GLint (Fin n) O ↔ g ∈ Formalism.UG.GLint (Fin n) O :=
  (mem_iff_invT (RingEquiv.refl L) (O := O) (O' := O) (fun _ => Iff.rfl) g).symm


open GlobalTheory.LFun.ConjPlace in
theorem invT_mem_doset (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (g : GL (Fin n) (w.adicCompletion E)) : ∃ a ∈ KGL w (n := n), ∃ b ∈ KGL w (n := n),
      invT (RingEquiv.refl _) n g = a * g⁻¹ * b := by
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV (E := E) w
  have hϖO : ϖ ∈ Formalism.UG.Ov E w := by
    change Valued.v ϖ ≤ 1
    unfold Formalism.UG.IsUnifV at hϖ
    rw [hϖ]
    exact (WithZero.exp_le_exp.mpr (by norm_num : (-1:ℤ) ≤ 0)).trans (le_of_eq WithZero.exp_zero)
  obtain ⟨ex, -, k₁, hk₁, k₂, hk₂, hg⟩ := Formalism.UG.Final.CartanDecomp E w n ϖ hϖO hϖ g
  set d : GL (Fin n) (w.adicCompletion E) := k₁⁻¹ * g * k₂⁻¹ with hd
  have hdv : (d : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Formalism.UG.diagPow E w ϖ ex := by
    rw [hd, Units.val_mul, Units.val_mul, hg, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc,
      Units.mul_inv, mul_one]
  have hsym : (d : Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵀ = (d : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    rw [hdv, Formalism.UG.diagPow, Matrix.diagonal_transpose]
  have hgd : g = k₁ * d * k₂ := by rw [hd]; group
  set θ := invT (RingEquiv.refl (w.adicCompletion E)) n
  refine ⟨θ k₁ * k₂, (KGL w (n := n)).mul_mem ((invT_mem_iff _ _).2 hk₁) hk₂,
    k₁ * θ k₂, (KGL w (n := n)).mul_mem hk₁ ((invT_mem_iff _ _).2 hk₂), ?_⟩
  have hθd : θ d = d⁻¹ := invT_of_symm d hsym
  rw [hgd, map_mul, map_mul, hθd, hd]
  group

end GlobalTheory.ChainOnto.CosetSymGL


open GlobalTheory.ChainOnto.CosetSymGL GlobalTheory.LFun.ConjPlace in
theorem GlobalTheory.ChainOnto.kGL_commensurated_cosetSym : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ), IsCommensurated (KGL w (n := n)) ∧ CosetSym (KGL w (n := n)) := fun E _ _ w n =>
  ⟨Formalism.UG.Final.GLintComm E w n, cosetSym_of_aut _ (invT (RingEquiv.refl _) n) (fun x => invT_mem_iff _ x)
    (invT_mem_doset E w n)⟩
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralGLCommensuratedDoubleCosetCardInvSymmStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integral_GL_commensurated_doubleCosetCardInvSymm : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ), IsCommensurated (KGL w (n := n)) ∧ CosetSym (KGL w (n := n)) := by
  first | exact @GlobalTheory.ChainOnto.kGL_commensurated_cosetSym | exact GlobalTheory.ChainOnto.kGL_commensurated_cosetSym | (intros; apply GlobalTheory.ChainOnto.kGL_commensurated_cosetSym <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeEsymmScaledMultisetAddSegmentStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.satake_esymm_scaled_multiset_add_segment : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a t k : ℕ) (B : Multiset ℂˣ) (z y : ℂˣ), B.card = a → k ≤ a + t → satEig (qV E w) (a + t) (B.map (z * y⁻¹ * ·) + seg w z t) k = ∑ j ∈ Finset.range (a + 1), (if j ≤ k then (qV E w : ℂ) ^ ((a - j) * (k - j)) * (Formalism.L2.Col.gaussBin (qV E w) t (k - j) : ℂ) * ((z : ℂ) * ((Real.sqrt (qV E w) : ℂ) ^ a)⁻¹) ^ k * (((y : ℂ))⁻¹ * (Real.sqrt (qV E w) : ℂ) ^ (a + t)) ^ j else 0) * satEig (qV E w) a B j := by
  first | exact @GlobalTheory.ChainOnto.satEig_map_add_seg | exact GlobalTheory.ChainOnto.satEig_map_add_seg | (intros; apply GlobalTheory.ChainOnto.satEig_map_add_seg <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeVectorIffInverseDoubleCosetsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.satake_vector_iff_inverse_doubleCosets : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (x : V) (B : Multiset ℂˣ), x ≠ 0 → x ∈ fixed ρ (KGL w (n := n)) → B.card = n → (IsSatVecGL w ρ x B ↔ ∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n, heckeVec ρ (KGL w (n := n)) (fun g => Tj ℂ n (Ov E w) ϖ j g⁻¹) x = satEig (qV E w) n (B.map (·⁻¹)) j • x) := by
  first | exact @GlobalTheory.ChainOnto.SatInv.satVec_iff_inv | exact GlobalTheory.ChainOnto.SatInv.satVec_iff_inv | (intros; apply GlobalTheory.ChainOnto.SatInv.satVec_iff_inv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterTransferSplitPlace

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.SplitTransfer

theorem seg_map_inv {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : ℂˣ) (t : ℕ) :
    (GlobalTheory.LFun.seg w x t).map (·⁻¹) = GlobalTheory.LFun.seg w x⁻¹ t := by
  have hr : (Finset.range t).image (fun i => t - 1 - i) = Finset.range t := by
    ext i
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩; omega
    · intro hi; exact ⟨t - 1 - i, by omega, by omega⟩
  have hinj : Set.InjOn (fun i => t - 1 - i) (Finset.range t : Set ℕ) := fun a ha b hb e => by
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    simp only at e
    omega
  unfold GlobalTheory.LFun.seg
  conv_rhs => rw [← hr, Finset.image_val_of_injOn hinj, Multiset.map_map]
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl fun i hi => ?_
  have hi' : i < t := Finset.mem_range.1 hi
  simp only [Function.comp_apply, mul_inv]
  congr 1
  apply Units.ext
  simp only [Units.val_inv_eq_inv_val, GlobalTheory.LFun.coe_npowU, GlobalTheory.LFun.npow]
  rw [← Complex.cpow_neg]
  congr 1
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring



theorem transferOn_isSplit : ∀ D : D7, TransferOn D fun v => IsSplit (E := D.host.E) v := by
  intro D ψ S T χS χT om hW t ht v hv hunr w h U hU f hf X _ _ ρ x B hx X' _ _ ρ' b hb hne
  obtain ⟨eS, heS⟩ := (GlobalTheory.T.exists_unitaryCharts_allFinitePlaces_frameLattice D S v w h).1 hv
  obtain ⟨eT, heT⟩ := (GlobalTheory.T.exists_unitaryCharts_allFinitePlaces_frameLattice D T v w h).1 hv
  have hxS := hx.isSatVecGL hv heS
  obtain ⟨hfix, hH⟩ := GlobalTheory.T.latticeVacuum_heckeIdentity_splitPlace_charts D ψ S T χS χT om hW t ht v w h hv hunr eS eT heS heT (f : WO S T → ℂ) hf
  obtain ⟨hcS, hsS⟩ := GlobalTheory.T.integral_GL_commensurated_doubleCosetCardInvSymm D.host.E w S.rank
  obtain ⟨hcT, hsT⟩ := GlobalTheory.T.integral_GL_commensurated_doubleCosetCardInvSymm D.host.E w T.rank
  let σF : Representation ℂ (GL (Fin S.rank) (w.adicCompletion D.host.E)) (WO S T → ℂ) :=
    ((om.comp (MonoidHom.inl _ _)).comp (embV S v)).comp eS.symm.toMonoidHom
  let πF : Representation ℂ (GL (Fin T.rank) (w.adicCompletion D.host.E)) (WO S T → ℂ) :=
    ((om.comp (MonoidHom.inr _ _)).comp (embV T v)).comp eT.symm.toMonoidHom
  have eσ : ∀ g, σF g = om (embV S v (eS.symm g), embV T v 1) := fun g => by simp [σF]
  have eπ : ∀ g, πF g = om (embV S v 1, embV T v (eT.symm g)) := fun g => by simp [πF]
  let σU := σF.subrepresentation U fun g u hu => by rw [Submodule.mem_comap, eσ]; exact hU _ _ u hu
  let πU := πF.subrepresentation U fun g u hu => by rw [Submodule.mem_comap, eπ]; exact hU _ _ u hu
  let ρS := ρ.comp eS.symm.toMonoidHom
  let ρT := ρ'.comp eT.symm.toMonoidHom

  have hKS : ∀ k ∈ KGL w (n := S.rank), eS.symm k ∈ Kv S v := fun k hk => (heS.2 (eS.symm k)).2 (by simpa using hk)
  have hKT : ∀ k ∈ KGL w (n := T.rank), eT.symm k ∈ Kv T v := fun k hk => (heT.2 (eT.symm k)).2 (by simpa using hk)
  have hfS : f ∈ fixed σU (KGL w (n := S.rank)) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (by
    change σF k (f : WO S T → ℂ) = f
    rw [eσ]; exact hfix _ (hKS k hk) _ (one_mem _))
  have hfT : f ∈ fixed πU (KGL w (n := T.rank)) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (by
    change πF k (f : WO S T → ℂ) = f
    rw [eπ]; exact hfix _ (one_mem _) _ (hKT k hk))
  have hequiv : ∀ g (u : U), (b.flip x) (πU g u) = ρT g ((b.flip x) u) := fun g u => by
    have e := hb 1 (eT.symm g) u x
    rw [show ρ 1 x = x by simp] at e
    rw [LinearMap.flip_apply, LinearMap.flip_apply]
    change b (πU g u) x = ρ' (eT.symm g) (b u x)
    rw [← e]
    congr 2
    exact Subtype.ext (by change πF g (u : WO S T → ℂ) = _; rw [eπ])
  have hinv : ∀ g (u : U) y, b (σU g u) (ρS g y) = b u y := fun g u y => by
    have e := hb (eS.symm g) 1 u y
    rw [show ρ' 1 (b u y) = b u y by simp] at e
    rw [← e]
    congr 2
    exact Subtype.ext (by change σF g (u : WO S T → ℂ) = _; rw [eσ])
  have hbfix : b f x ∈ fixed ρT (KGL w (n := T.rank)) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
    have e := hequiv k f
    rw [GlobalTheory.LGrp.mem_fixed.1 hfT k hk] at e
    exact e.symm
  have hcard : (stepPar χS χT t (fun _ => B) w).card = T.rank := by
    simp [stepPar, GlobalTheory.LFun.seg, hxS.2.2.1, ht]
  have hB'inv : (stepPar χS χT t (fun _ => B) w).map (·⁻¹) =
      (B.map (·⁻¹)).map ((val (F := D.host.F) χS w)⁻¹ * ((val (F := D.host.F) χT w)⁻¹)⁻¹ * ·) +
        GlobalTheory.LFun.seg w (val (F := D.host.F) χS w)⁻¹ t := by
    rw [stepPar, Multiset.map_add (f := _), seg_map_inv, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun c _ => ?_
    simp only [Function.comp_apply, mul_inv]
  refine Or.inl ⟨hv, eT, heT, (GlobalTheory.T.satake_vector_iff_inverse_doubleCosets D.host.E w T.rank X' ρT (b f x) _ hne hbfix hcard).2 fun ϖ hϖ k hk => ?_⟩
  have hsubT : ∀ g (y : U), U.subtype (πU g y) = πF g (U.subtype y) := fun g y => rfl
  have hsubS : ∀ g (y : U), U.subtype (σU g y) = σF g (U.subtype y) := fun g y => rfl
  have hInvT : (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) ∈ Hecke ℂ (KGL w (n := T.rank)) :=
    (GlobalTheory.T.hecke_operator_move_across_invariant_bilinear _ (KGL w (n := T.rank)) hcT hsT ℂ ℂ ℂ 1 1 0 (fun _ _ _ => by simp) 0 (zero_mem _) 0 (zero_mem _) _
      (Tj_mem_hecke hϖ k)).1
  let cf : ℕ → ℂ := fun j => if j ≤ k then (qV D.host.E w : ℂ) ^ ((S.rank - j) * (k - j)) *
    (Formalism.L2.Col.gaussBin (qV D.host.E w) t (k - j) : ℂ) *
    (((val (F := D.host.F) χS w : ℂˣ) : ℂ) * (Real.sqrt (qV D.host.E w) : ℂ) ^ S.rank)⁻¹ ^ k *
    (((val (F := D.host.F) χT w : ℂˣ) : ℂ) * (Real.sqrt (qV D.host.E w) : ℂ) ^ T.rank) ^ j else 0
  have hH' : heckeVec πF (KGL w (n := T.rank)) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) (U.subtype f) =
      ∑ j ∈ Finset.range (S.rank + 1), cf j • heckeVec σF (KGL w (n := S.rank)) (Tj ℂ S.rank (Ov D.host.E w) ϖ j) (U.subtype f) :=
    hH ϖ hϖ k hk
  have e1 : U.subtype (heckeVec πU (KGL w (n := T.rank)) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) f) =
      heckeVec πF (KGL w (n := T.rank)) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) (U.subtype f) :=
    map_heckeVec hcT hInvT U.subtype hsubT f
  have e2 : ∀ j, U.subtype (heckeVec σU (KGL w (n := S.rank)) (Tj ℂ S.rank (Ov D.host.E w) ϖ j) f) =
      heckeVec σF (KGL w (n := S.rank)) (Tj ℂ S.rank (Ov D.host.E w) ϖ j) (U.subtype f) := fun j =>
    map_heckeVec hcS (Tj_mem_hecke hϖ j) U.subtype hsubS f
  have hT : heckeVec πU (KGL w (n := T.rank)) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) f =
      ∑ j ∈ Finset.range (S.rank + 1), cf j • heckeVec σU (KGL w (n := S.rank)) (Tj ℂ S.rank (Ov D.host.E w) ϖ j) f := by
    apply U.injective_subtype

    rw [e1, hH', map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, e2 j]
  have hmove : ∀ j ∈ Finset.range (S.rank + 1), b (heckeVec σU (KGL w (n := S.rank)) (Tj ℂ S.rank (Ov D.host.E w) ϖ j) f) x =
      satEig (qV D.host.E w) S.rank (B.map (·⁻¹)) j • b f x := by
    intro j hj
    rw [(GlobalTheory.T.hecke_operator_move_across_invariant_bilinear _ _ hcS hsS U X X' σU ρS b hinv f hfS x hxS.2.1 _ (Tj_mem_hecke hϖ j)).2,
      (GlobalTheory.T.satake_vector_iff_inverse_doubleCosets D.host.E w S.rank X ρS x B hxS.1 hxS.2.1 hxS.2.2.1).1 hxS ϖ hϖ j
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)), map_smul]
  have hsym := GlobalTheory.T.satake_esymm_scaled_multiset_add_segment D.host.E w S.rank t k (B.map (·⁻¹)) (val (F := D.host.F) χS w)⁻¹
    (val (F := D.host.F) χT w)⁻¹ (by rw [Multiset.card_map, hxS.2.2.1]) (ht ▸ hk)
  calc heckeVec ρT (KGL w (n := T.rank)) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) (b f x)
      = b (heckeVec πU (KGL w (n := T.rank)) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) f) x :=
        (map_heckeVec hcT hInvT (b.flip x) hequiv f).symm
    _ = ∑ j ∈ Finset.range (S.rank + 1), cf j • satEig (qV D.host.E w) S.rank (B.map (·⁻¹)) j • b f x := by

        rw [hT, map_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [map_smul, LinearMap.smul_apply, hmove j hj]
    _ = satEig (qV D.host.E w) T.rank ((stepPar χS χT t (fun _ => B) w).map (·⁻¹)) k • b f x := by
        simp_rw [smul_smul]
        rw [← Finset.sum_smul]
        congr 1
        rw [hB'inv, ht, hsym]
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        simp only [cf]
        split_ifs
        · rw [ht]
          simp only [Units.val_inv_eq_inv_val, inv_inv, mul_inv]
        · rfl

end GlobalTheory.ChainOnto.SplitTransfer
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterTransferSplitPlaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.sphericalParameterTransfer_splitPlace : ∀ D : D7, TransferOn D fun v => IsSplit (E := D.host.E) v := by
  first | exact @GlobalTheory.ChainOnto.SplitTransfer.transferOn_isSplit | exact GlobalTheory.ChainOnto.SplitTransfer.transferOn_isSplit | (intros; apply GlobalTheory.ChainOnto.SplitTransfer.transferOn_isSplit <;> assumption)
end
end
