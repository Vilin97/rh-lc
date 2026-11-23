module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.JoinType
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivPiExteriorTensorBlockLevi
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HintConstMulSum
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IrreducibleSmoothAdmissibleGL
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HkMemFixed
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthOfProductsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeAlgebraStructure
import GroundTheory.LocalFields.PadicLogSeries
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.PeakCone

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientOfNonNilpotent

section

@[expose] public section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

namespace GlobalTheory.CompanionTheory.HeckeSub

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem finite_cosets {K : Subgroup (GL ι F)} {e : GL ι F → ℂ} (hE : IsHk K e) :
    {q : GL ι F ⧸ K | e q.out ≠ 0}.Finite := by
  have hc : IsCompact (tsupport e) := hE.2.2.1
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun g : GL ι F => (fun x => g⁻¹ * x) ⁻¹' (K : Set (GL ι F)))
    (fun g => hE.1.preimage (continuous_const.mul continuous_id))
    (fun g _ => Set.mem_iUnion.2 ⟨g, by simp [K.one_mem]⟩)
  refine (t.finite_toSet.image (fun g => (QuotientGroup.mk g : GL ι F ⧸ K))).subset fun q hq => ?_
  have hq' : q.out ∈ tsupport e := subset_tsupport _ hq
  obtain ⟨g, hg, hgq⟩ := Set.mem_iUnion₂.1 (ht hq')
  exact ⟨g, hg, (QuotientGroup.eq.2 hgq).trans (QuotientGroup.out_eq' q)⟩

theorem hk_map {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GL ι F) V) (σ : Representation ℂ (GL ι F) W) (f : V →ₗ[ℂ] W)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) {K : Subgroup (GL ι F)} {e : GL ι F → ℂ} (hE : IsHk K e) (v : V) :
    f (hk ρ K e v) = hk σ K e (f v) := by
  unfold hk
  have hfin : (Function.support fun q : GL ι F ⧸ K => e q.out • ρ q.out v).Finite :=
    (finite_cosets hE).subset fun q hq h0 => hq (by simp [show e q.out = 0 from h0])
  rw [map_finsum f hfin]
  simp only [map_smul, hf]

end GlobalTheory.CompanionTheory.HeckeSub
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientOfNonNilpotentVariant

section

@[expose] public section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

namespace GlobalTheory.CompanionTheory.HeckeSub

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_iterate_eq_zero_of_subquot {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    {K : Subgroup (GL ι F)} {e : GL ι F → ℂ} (hE : IsHk K e) (π : Representation ℂ (GL ι F) V)
    (ρ : Representation ℂ (GL ι F) U) (hρ : IsSmooth ρ) (hfl : HasFiniteLength ρ)
    (hkill : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL ι F) W), IsSmooth τ →
      τ.IsIrreducible → IsSubquotient τ ρ → IsEmpty (τ.Equiv π) → ∀ w ∈ fixed τ K, hk τ K e w = 0)
    (hns : ¬ IsSubquotient π ρ) (S : Subrepresentation ρ) :
    ∃ r : ℕ, ∀ u ∈ S.toSubmodule, u ∈ fixed ρ K → (hk ρ K e)^[r] u = 0 := by
  obtain ⟨hGT, hLT⟩ := (hasFiniteLength_iff_wellFounded ρ).1 hfl
  induction S using WellFoundedLT.induction with
  | ind S ih =>
    by_cases hS : S = ⊥
    · subst hS
      exact ⟨0, fun u hu _ => hu⟩
    obtain ⟨T, hT, hmax⟩ := (wellFounded_gt (α := Subrepresentation ρ)).has_min {T | T < S}
      ⟨⊥, bot_lt_iff_ne_bot.2 hS⟩
    have hcov : T ⋖ S := ⟨hT, fun c h1 h2 => hmax c h2 h1⟩
    let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
    have hsq : IsSubquotient (subQuot S T) ρ := ⟨S, p, Submodule.mkQ_surjective _⟩
    have hne : IsEmpty ((subQuot S T).Equiv π) := ⟨fun φ => hns
      ((IsSubquotient.trans (IsSubquotient.of_injective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.injective) hsq))⟩
    obtain ⟨r, hr⟩ := ih T hT
    refine ⟨r + 1, fun u huS hufix => ?_⟩
    have hfixS : (Submodule.mkQ _ (⟨u, huS⟩ : S.toSubmodule) :
        S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) ∈ fixed (subQuot S T) K := by
      intro h
      have h1 : ρ (h : GL ι F) u = u := by simpa using hufix h
      have h2 : S.toRepresentation (h : GL ι F) ⟨u, huS⟩ = ⟨u, huS⟩ := Subtype.ext h1
      simp only [MonoidHom.one_apply, Units.val_one, one_smul]
      exact congrArg (Submodule.mkQ _) h2
    have h0 := hkill _ (subQuot S T) (hsq.isSmooth hρ) (isIrreducible_subQuot hcov) hsq hne _ hfixS
    have h1 : (hk S.toRepresentation K e ⟨u, huS⟩ : S.toSubmodule).1 = hk ρ K e u :=
      hk_map S.toRepresentation ρ S.toSubmodule.subtype (fun _ _ => rfl) hE ⟨u, huS⟩
    have h2 := hk_map S.toRepresentation (subQuot S T) (Submodule.mkQ _) (fun _ _ => rfl) hE ⟨u, huS⟩
    rw [h0] at h2
    have h3 : hk ρ K e u ∈ T.toSubmodule := by
      rw [← h1]
      exact (Submodule.Quotient.mk_eq_zero (T.toSubmodule.comap S.toSubmodule.subtype)).1 h2
    rw [Function.iterate_succ_apply]
    exact hr _ h3 (GlobalTheory.CompanionTheory.HeckeFix.hk_mem_fixed F ι K e hE U ρ u hufix).1

end GlobalTheory.CompanionTheory.HeckeSub
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientOfNonNilpotentVariantStatement

section

@[expose] public section

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (ι : Type) [Fintype ι] [DecidableEq ι]

namespace PositivityTheory.Rg.BcN.F2

open GlobalTheory.PRep (IsSmooth fixed)
open GlobalTheory.SmGL (HasFiniteLength IsSubquotient)

/-- A finite-length smooth representation contains `π` as a subquotient if the Hecke operator
acts non-nilpotently on its `K`-fixed vectors and vanishes on the fixed vectors of every
irreducible smooth subquotient inequivalent to `π`. -/
def SubOfNonNil' : Prop :=
  ∀ (K : Subgroup (GL ι F)) (e : GL ι F → ℂ), IsHk K e →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL ι F) V), IsSmooth π → π.IsIrreducible →
    ∀ (U : Type) [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ (GL ι F) U), IsSmooth ρ → HasFiniteLength ρ →
    (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL ι F) W), IsSmooth τ → τ.IsIrreducible →
      IsSubquotient τ ρ → IsEmpty (τ.Equiv π) → ∀ w ∈ fixed τ K, hk τ K e w = 0) →
    (∀ r : ℕ, ∃ u ∈ fixed ρ K, (hk ρ K e)^[r] u ≠ 0) → IsSubquotient π ρ

end PositivityTheory.Rg.BcN.F2

namespace GlobalTheory.T

open PositivityTheory.Rg.BcN.F2 (SubOfNonNil') in
open GlobalTheory.CompanionTheory.HeckeSub (exists_iterate_eq_zero_of_subquot) in
/-- A Hecke operator that vanishes on the fixed vectors of all irreducible
subquotients inequivalent to `π` can act non-nilpotently only if `π` occurs. -/
theorem subquotient_of_non_nilpotent_variant : SubOfNonNil' F ι := by
  intro K e hE V _ _ π _ _ U _ _ ρ hρ hfl hkill hNonNilpotent
  by_contra hNotSubquotient
  obtain ⟨r, hIterateZero⟩ :=
    exists_iterate_eq_zero_of_subquot hE π ρ hρ hfl hkill hNotSubquotient (⊤ : Subrepresentation ρ)
  obtain ⟨u, hu, hIterateNeZero⟩ := hNonNilpotent r
  exact hIterateNeZero (hIterateZero u Submodule.mem_top hu)

end GlobalTheory.T
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeAlgebraStructureStatement

section

@[expose] public section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

theorem _root_.GlobalTheory.T.hecke_algebra_structure : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι], HkAlg F ι := by
  first | exact @GlobalTheory.CompanionTheory.HeckeAlg.hk_alg | exact GlobalTheory.CompanionTheory.HeckeAlg.hk_alg | (intros; apply GlobalTheory.CompanionTheory.HeckeAlg.hk_alg <;> assumption)
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocFinal

section

@[expose] public section

namespace PositivityTheory.Rg.BcN.F2.Final

open PositivityTheory.Rg.BcN.F2

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (ι : Type) [Fintype ι] [DecidableEq ι]

theorem hkAlg : HkAlg F ι := GlobalTheory.T.hecke_algebra_structure F ι
theorem prodFinLen : ProdFinLen F ι := GlobalTheory.T.finite_length_of_products F ι
theorem subOfNonNil' : SubOfNonNil' F ι :=
  GlobalTheory.T.subquotient_of_non_nilpotent_variant F ι

end PositivityTheory.Rg.BcN.F2.Final
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PScFin

section

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Tail.PSc

section Gen

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem hk_zero' (ρ : Representation ℂ (GL ι F) V) (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) : hk ρ K e 0 = 0 := by
  simp [hk]

theorem hk_supp (ρ : Representation ℂ (GL ι F) V) (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) (he : IsHk K e) (v : V) :
    Function.HasFiniteSupport fun q : GL ι F ⧸ K => e q.out • ρ q.out v := by
  refine (GlobalTheory.CompanionTheory.DiagAvg.finite_cosets K he.1 e he.2.2.1).subset fun q hq => ?_
  intro h0
  exact hq (by simp [show e q.out = 0 from h0])

theorem hk_add' (ρ : Representation ℂ (GL ι F) V) (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) (he : IsHk K e) (v w : V) :
    hk ρ K e (v + w) = hk ρ K e v + hk ρ K e w := by
  unfold hk
  rw [← finsum_add_distrib (hk_supp ρ K e he v) (hk_supp ρ K e he w)]
  exact finsum_congr fun q => by rw [map_add (f := _), smul_add]

theorem hk_smul' (ρ : Representation ℂ (GL ι F) V) (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) (c : ℂ) (v : V) :
    hk ρ K e (c • v) = c • hk ρ K e v := by
  unfold hk
  rw [smul_finsum]
  exact finsum_congr fun q => by rw [map_smul, smul_comm]

def hkEnd (ρ : Representation ℂ (GL ι F) V) (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) (he : IsHk K e) :
    Module.End ℂ (fixed ρ K) where
  toFun v := ⟨hk ρ K e v.1, ((PositivityTheory.Rg.BcN.F2.Final.hkAlg F ι) K e e he he).2.2 V ρ v.1 v.2 |>.1⟩
  map_add' v w := Subtype.ext (hk_add' ρ K e he v.1 w.1)
  map_smul' c v := Subtype.ext (hk_smul' ρ K e c v.1)

theorem hkEnd_pow (ρ : Representation ℂ (GL ι F) V) (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) (he : IsHk K e) (k : ℕ) :
    ∀ x : fixed ρ K, ((hkEnd ρ K e he ^ k) x).1 = (hk ρ K e)^[k] x.1 := by
  induction k with
  | zero => intro x; rfl
  | succ k ih =>
    intro x
    rw [pow_succ, Module.End.mul_apply, ih, Function.iterate_succ_apply]
    rfl

theorem hk_iter_zero (ρ : Representation ℂ (GL ι F) V) (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) (k : ℕ) :
    (hk ρ K e)^[k] 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, hk_zero', ih]

theorem nonnil_of_pow (ρ : Representation ℂ (GL ι F) V) (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) (he : IsHk K e)
    [FiniteDimensional ℂ (fixed ρ K)] (m : ℕ) (hdim : Module.finrank ℂ (fixed ρ K) ≤ m) (u : V) (hu : u ∈ fixed ρ K)
    (hne : (hk ρ K e)^[m] u ≠ 0) : ∀ r : ℕ, ∃ u ∈ fixed ρ K, (hk ρ K e)^[r] u ≠ 0 := by
  intro r
  rcases le_total r m with hr | hr
  · refine ⟨u, hu, fun h0 => hne ?_⟩
    have : m = (m - r) + r := (Nat.sub_add_cancel hr).symm
    rw [this, Function.iterate_add_apply, h0, hk_iter_zero]
  · by_contra hall
    push_neg at hall
    set T := hkEnd ρ K e he
    have hker : LinearMap.ker (T ^ r) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [LinearMap.mem_ker]
      exact Subtype.ext (by rw [hkEnd_pow]; exact hall x.1 x.2)
    have e1 := Module.End.ker_pow_eq_ker_pow_finrank_of_le (f := T) (le_trans hdim hr)
    have e2 := Module.End.ker_pow_eq_ker_pow_finrank_of_le (f := T) hdim
    have hm : (⟨u, hu⟩ : fixed ρ K) ∈ LinearMap.ker (T ^ m) := by
      rw [e2, ← e1, hker]; trivial
    rw [LinearMap.mem_ker] at hm
    apply hne
    have := congrArg Subtype.val hm
    rw [hkEnd_pow] at this
    exact this

end Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem sub_of_pow {n : ℕ} (D : Pre E n) (w : Pl E) (K' : Subgroup (GLw n w)) (e : GLw n w → ℂ) (he : IsHk K' e)
    (P : SmIrr (GLw n w))
    (hkill : ∀ τ : SmIrr (GLw n w), GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt D w) → IsEmpty (τ.ρ.Equiv P.ρ) →
      ∀ v ∈ fixed τ.ρ K', hk τ.ρ K' e v = 0)
    (m : ℕ) (hdim : Module.finrank ℂ (fixed (prodAt D w) K') < m) (u : _) (hu : u ∈ fixed (prodAt D w) K')
    (hne : (hk (prodAt D w) K' e)^[m - 1] u ≠ 0) : GlobalTheory.SmGL.IsSubquotient P.ρ (prodAt D w) := by
  have hsm : GlobalTheory.PRep.IsSmooth (prodAt D w) := GlobalTheory.SmGL.isSmooth_parInd _ _
  have hfl : GlobalTheory.SmGL.HasFiniteLength (prodAt D w) :=
    PositivityTheory.Rg.BcN.F2.Final.prodFinLen (w.adicCompletion E) (Fin n) (Fin D.c) (fun i => Fin (D.N i))
      (GlobalTheory.SmGL.stdBlocks D.N D.h) (fun i => (D.σ i w).V) (fun i => (D.σ i w).ρ) (fun i => (D.σ i w).smooth)
      (fun i => (D.σ i w).irred)
  haveI : FiniteDimensional ℂ (fixed (prodAt D w) K') :=
    GlobalTheory.LeviFactor.finiteDimensional_fixed_of_hasFiniteLength
      (fun Y _ _ π hs hi => GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible (w.adicCompletion E) (Fin n) Y π hs hi)
      hsm hfl K' he.1 he.2.1
  refine PositivityTheory.Rg.BcN.F2.Final.subOfNonNil' (w.adicCompletion E) (Fin n) K' e he P.V P.ρ P.smooth P.irred _
    (prodAt D w) hsm hfl ?_ ?_
  · intro W _ _ τ hs hi hsub hemp v hv
    exact hkill ⟨W, τ, hs, hi⟩ hsub hemp v hv
  · exact nonnil_of_pow (prodAt D w) K' e he (m - 1) (by omega) u hu hne

end PositivityTheory.Rg.BcB.F.Tail.PSc

end
end
end
