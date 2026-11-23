module

public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodLem
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeAlgebraCompUnitaryGroupAntidiagTransportMemStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertHeckeOperatorIndepOfInertDatumStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleRepIsotypicOfCentraliserFactorStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitarySatakeInvariantAntidiagTransportStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryTorusUnipotentCosetTransportIffStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GEquivIntL
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalIntegrality
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSplitPlace
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FixedNeBotOfEquiv
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingHomExtAdicCompletion

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.RowPar

section Sat
open Formalism.UG GlobalTheory.SatInd

theorem satAtS_indep {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Submodule ℂ (GAf L n → W)) {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}
    (Dv Dv' : InertDatum L n v w) (α : Fin (n / 2) → ℂ) (hs : NG.SatAtS S Dv α) : NG.SatAtS S Dv' α := by
  obtain ⟨f, hfS, hf0, U, hU, hUv, hH⟩ := hs
  refine ⟨f, hfS, hf0, U, hU, hUv, fun h' hh' => ?_⟩
  have hm : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
  rw [GlobalTheory.T.inertHeckeOperator_indep_of_inertDatum L n v w Dv Dv' U _ h' hh'.1 f,
    hH _ (GlobalTheory.T.heckeAlgebra_comp_unitaryGroupAntidiagTransport_mem (gEquiv Dv Dv') (gEquiv_comm Dv Dv') (gEquiv_intL Dv Dv') n h' hh'),
    GlobalTheory.T.unitarySatake_invariant_antidiagTransport (gEquiv Dv Dv') (gEquiv_comm Dv Dv') (gEquiv_intL Dv Dv') Dv.ϖ Dv'.ϖ _ n (n / 2) h' hh'.1
      (GlobalTheory.T.unitaryTorus_unipotent_coset_transport_iff (gEquiv Dv Dv') (gEquiv_comm Dv Dv') (gEquiv_intL Dv Dv') Dv.ϖ Dv'.ϖ _ _ n (n / 2)
        Dv.unram Dv'.unram hm)]

end Sat

section Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.SmGL GlobalTheory.LocLanglands

theorem ringHom_ext_adicCompletion {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {R : Type} [Ring R]
    [TopologicalSpace R] [T2Space R] (f g : v.adicCompletion K →+* R) (hf : Continuous f) (hg : Continuous g)
    (h : ∀ y : K, f (algebraMap K _ y) = g (algebraMap K _ y)) : f = g :=
  DFunLike.coe_injective ((HeightOneSpectrum.denseRange_algebraMap K v).equalizer hf hg (funext h))

theorem splitEmb_eq {L : Type} [Field L] [NumberField L] [IsCMField L] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (w : HeightOneSpectrum (𝓞 L)) (si si' : L →ₐ[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L))
    (i i' : v.adicCompletion (maximalRealSubfield L) ≃+* w.adicCompletion L) (hi : Continuous i) (hi' : Continuous i')
    (hix : ∀ x, i (si x) = algebraMap L _ x) (hix' : ∀ x, i' (si' x) = algebraMap L _ x) : si' = si ∧ i' = i := by
  have e : (i' : v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L) = i := by
    refine ringHom_ext_adicCompletion v _ _ hi' hi fun y => ?_
    have h1 := hix (algebraMap _ L y)
    have h2 := hix' (algebraMap _ L y)
    rw [AlgHom.commutes] at h1 h2
    exact h2.trans h1.symm
  have e' : i' = i := RingEquiv.ext fun x => congrArg (fun f : v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L => f x) e
  refine ⟨AlgHom.ext fun x => i.injective ?_, e'⟩
  rw [hix, ← hix' x, e']

theorem splitPlace_eq_of_isLocS {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (S S' : Submodule ℂ (GAf L n → W)) (s s' : SplitPlace L) (h : s'.w = s.w)
    (τ : IrrRep (GL (Fin n) (s.w.adicCompletion L))) (τ' : IrrRep (GL (Fin n) (s'.w.adicCompletion L)))
    (hτ : IsLocS S s τ) (hτ' : IsLocS S' s' τ') : s' = s := by
  obtain ⟨i, -, hi, hix, -⟩ := hτ
  obtain ⟨i', -, hi', hix', -⟩ := hτ'
  have hv : s'.v = s.v := HeightOneSpectrum.ext (by rw [← s'.w_under, ← s.w_under, h])
  have key : ∀ (w : HeightOneSpectrum (𝓞 L)) (hw : s'.w = w)
      (j : s'.v.adicCompletion (maximalRealSubfield L) ≃+* w.adicCompletion L), Continuous j →
      (∀ x, j (s'.i x) = algebraMap L _ x) → s' = s := by
    intro w hw j hj hjx
    rw [h] at hw
    subst hw
    obtain ⟨v, si⟩ := s
    obtain ⟨v', si'⟩ := s'
    dsimp only at hv
    subst hv
    obtain rfl := (splitEmb_eq _ _ si si' i j hi hj hix hjx).1
    rfl
  exact key _ rfl i' hi' hix'

theorem cl_eq_of_isLocS {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (π : NG.FinTyp L n) (s : SplitPlace L)
    (τ τ' : IrrRep (GL (Fin n) (s.w.adicCompletion L))) (hτ : IsLocS π.S s τ) (hτ' : IsLocS π.S s τ') : τ.cl = τ'.cl := by
  obtain ⟨i, T, hi, hix, hTi, hTS, hTe⟩ := hτ
  obtain ⟨i', T', hi', hix', hTi', hTS', hTe'⟩ := hτ'
  obtain rfl := (splitEmb_eq s.v s.w s.i s.i i' i hi' hi hix' hix).2
  obtain ⟨hdec, hcom, huniq⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  choose sec hsec using fun A => (huniq A).exists
  have sec_eq : ∀ x : GAf L n, TrivOutside {s.v} x → sec (s.loc n x) = x := fun x hx =>
    (huniq _).unique (hsec _) ⟨hx, rfl⟩
  have triv_mul : ∀ x y : GAf L n, TrivOutside {s.v} x → TrivOutside {s.v} y → TrivOutside {s.v} (x * y) := by
    intro x y hx hy v hv
    have h1 := hx v hv
    have h2 := hy v hv
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [Matrix.map_mul, h1, h2, one_mul]
  have triv_one : TrivOutside {s.v} (1 : GAf L n) := by
    intro v _
    simp [Matrix.map_one]
  let sH : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) →* GAf L n :=
    { toFun := sec
      map_one' := (huniq 1).unique (hsec 1) ⟨triv_one, map_one _⟩
      map_mul' := fun A B => (huniq (A * B)).unique (hsec (A * B))
        ⟨triv_mul _ _ (hsec A).1 (hsec B).1, by rw [map_mul, (hsec A).2, (hsec B).2]⟩ }
  let ρ : Representation ℂ (GAf L n) π.S :=
    { toFun := fun g => (NG.rt L n g).restrict (fun f hf => π.stable g f hf)
      map_one' := LinearMap.ext fun f => Subtype.ext (funext fun x => by simp [NG.rt])
      map_mul' := fun g h => LinearMap.ext fun f => Subtype.ext (funext fun x => by simp [NG.rt, mul_assoc]) }
  have hρ : ρ.IsIrreducible := by
    refine (GlobalTheory.CuspRep.isIrreducible_iff ρ).2 ⟨Submodule.nontrivial_iff_ne_bot.2 π.ne, fun U hU => ?_⟩
    have hst : ∀ h, ∀ f ∈ U.map π.S.subtype, NG.rt L n h f ∈ U.map π.S.subtype := by
      rintro h _ ⟨u, hu, rfl⟩
      exact ⟨ρ h u, hU h u hu, rfl⟩
    rcases π.irr _ (Submodule.map_subtype_le _ _) hst with h0 | h1
    · left
      exact Submodule.map_injective_of_injective π.S.injective_subtype (h0.trans (Submodule.map_bot _).symm)
    · right
      refine Submodule.map_injective_of_injective π.S.injective_subtype ?_
      rw [h1, Submodule.map_subtype_top]
  let e : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) →* GL (Fin n) (s.w.adicCompletion L) :=
    Matrix.GeneralLinearGroup.map i.toRingHom
  have he : Function.Surjective e := fun B =>
    ⟨Matrix.GeneralLinearGroup.map i.symm.toRingHom B, Units.ext (Matrix.ext fun a b => by simp [e])⟩
  have hnt : ∀ τ₀ : IrrRep (GL (Fin n) (s.w.adicCompletion L)), Nontrivial τ₀.V := fun τ₀ =>
    ((GlobalTheory.CuspRep.isIrreducible_iff τ₀.ρ).1 τ₀.irr).1
  have key : ∀ (τ₀ : IrrRep (GL (Fin n) (s.w.adicCompletion L))) (T₀ : τ₀.V →ₗ[ℂ] (GAf L n → ℂ)),
      Function.Injective T₀ → (∀ a, T₀ a ∈ π.S) →
      (∀ x : GAf L n, TrivOutside {s.v} x → ∀ a,
        T₀ (τ₀.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) a) = NG.rt L n x (T₀ a)) →
      ∃ f : Representation.IntertwiningMap (τ₀.ρ.comp e) (ρ.comp sH), f ≠ 0 := by
    intro τ₀ T₀ hT₀ hS₀ he₀
    refine ⟨⟨LinearMap.codRestrict π.S T₀ hS₀, fun A => LinearMap.ext fun a => Subtype.ext ?_⟩, fun h0 => ?_⟩
    · have h1 := he₀ (sec A) (hsec A).1 a
      rw [(hsec A).2] at h1
      exact h1
    · haveI := hnt τ₀
      obtain ⟨a, ha⟩ := exists_ne (0 : τ₀.V)
      refine ha (hT₀ ?_)
      have h2 := congrArg (fun f : Representation.IntertwiningMap (τ₀.ρ.comp e) (ρ.comp sH) => (f a : GAf L n → ℂ)) h0
      simpa using h2
  obtain ⟨f, hf⟩ := @key τ T hTi hTS hTe
  obtain ⟨f', hf'⟩ := key τ' T' hTi' hTS' hTe'
  have hcomm : ∀ g, ∃ u, ∀ y, Commute ((sH u)⁻¹ * g) (sH y) := by
    intro g
    obtain ⟨x, y, hx, hy, rfl⟩ := hdec g
    refine ⟨s.loc n x, fun B => ?_⟩
    rw [show sH (s.loc n x) = x from sec_eq x hx, inv_mul_cancel_left]
    exact (hcom _ _ (hsec B).1 hy).symm
  obtain ⟨φ⟩ := (GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor _ _ _ _ _ ρ sH (τ.ρ.comp e) (τ'.ρ.comp e) hρ
    (GlobalTheory.CuspRep.ParLaws.isIrreducible_comp τ.irr e he) (GlobalTheory.CuspRep.ParLaws.isIrreducible_comp τ'.irr e he)
    hcomm f hf).2 f' hf'
  refine IrrRep.cl_eq_iff.2 ⟨Representation.Equiv.mk φ.toLinearEquiv fun B => ?_⟩
  obtain ⟨A, rfl⟩ := he B
  exact φ.isIntertwining' A

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)

def LocAt (σ : D.what₂.FT) (w : PlE D.host) : Type 1 :=
  {p : (s : SplitPlace D.host.E) × IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E)) //
    p.1.w = w ∧ IsLocS (rep σ).S p.1 p.2}

def unrW : RowWD D := by
  let m : Multiset ℂ := Multiset.replicate D.R.r 1
  have hm : (0 : ℂ) ∉ m := fun h => zero_ne_one (Multiset.eq_of_mem_replicate h)
  exact
    { par := fun _ w => GlobalTheory.WeilDeligne.WD.lpUnr (D.nd.plOm.2 w) m
      sat := fun _ _ => m
      dim := fun _ w =>
        (GlobalTheory.WeilDeligne.WD.lpUnr_spec (h := D.nd.plOm.2 w) m hm).2.2.trans
          (Multiset.card_replicate _ _)
      tame := fun _ k v =>
        GlobalTheory.WeilDeligne.WD.tame_of_unr
          (GlobalTheory.WeilDeligne.WD.lpUnr_spec (h := D.nd.plOm.2 (D.naut.plGw k v)) m hm).1 }

end Loc

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

def satOf (S : Submodule ℂ (GAf L n → W)) (w : HeightOneSpectrum (𝓞 L)) : Multiset ℂ := by
  classical
  exact if h : ∃ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ),
      NG.OverPl w v ∧ NG.SatAtS S Dv α then Finset.univ.val.map h.choose_spec.choose_spec.choose else 0

theorem satAtS_transfer (S : Submodule ℂ (GAf L n → W)) {w : HeightOneSpectrum (𝓞 L)}
    (v0 v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (Dv0 : InertDatum L n v0 w) (Dv : InertDatum L n v w)
    (hv : v0 = v) (α : Fin (n / 2) → ℂ) (hs : NG.SatAtS S Dv0 α) : NG.SatAtS S Dv α := by
  subst hv
  exact satAtS_indep S Dv0 Dv α hs

theorem satOf_spec (S : Submodule ℂ (GAf L n → W)) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (w : HeightOneSpectrum (𝓞 L)) (hO : NG.OverPl w v) (Dv : InertDatum L n v w) (hα : ∃ α, NG.SatAtS S Dv α) :
    ∃ α, NG.SatAtS S Dv α ∧ satOf S w = Finset.univ.val.map α := by
  classical
  obtain ⟨α, hα⟩ := hα
  have h : ∃ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ),
      NG.OverPl w v ∧ NG.SatAtS S Dv α := ⟨v, Dv, α, hO, hα⟩
  have hsp := h.choose_spec.choose_spec.choose_spec
  refine ⟨h.choose_spec.choose_spec.choose, satAtS_transfer S _ v _ Dv
    (HeightOneSpectrum.ext (hsp.1.symm.trans hO)) _ hsp.2, ?_⟩
  unfold satOf
  rw [dite_eq_left h]

end GlobalTheory.RowPar
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LpDimLocRec

section

@[expose] public section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.RowPar
section Sat
open Formalism.UG GlobalTheory.SatInd
end Sat
section Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.SmGL GlobalTheory.LocLanglands
theorem lpDim_locRec_alt {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (h : IsPlaceOver A w) {n : ℕ}
    (τ : IrrRep (GL (Fin n) (w.adicCompletion E))) : (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h (cls τ)).lpDim = n := by
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h); obtain ⟨_, _, _, H⟩ := hOpn) | obtain ⟨_, _, _, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h
  exact H.dim _
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
def weilDeligneParameterOfLocalDatum {σ : D.what₂.FT} {w : PlE D.host} (p : LocAt D rep σ w) :
    GlobalTheory.WeilDeligne.WD (E := D.host.E) (A := D.nd.plOm.1 w) (w := w) (D.nd.plOm.2 w) :=
  p.2.1 ▸ _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 p.1.1.w) (cls p.1.2)
def weilDeligneParameterAtPlace (σ : D.what₂.FT) (w : PlE D.host) :
    GlobalTheory.WeilDeligne.WD (E := D.host.E) (A := D.nd.plOm.1 w) (w := w) (D.nd.plOm.2 w) := by
  classical
  exact if h : Nonempty (LocAt D rep σ w) then _root_.GlobalTheory.RowPar.weilDeligneParameterOfLocalDatum hL D rep h.some else (unrW D).par σ w
theorem parameter_of_local_datum_eq_reciprocity {σ : D.what₂.FT} {w : PlE D.host} (p : LocAt D rep σ w) (s : SplitPlace D.host.E) (hs : s.w = w)
    (τ : IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E))) (hτ : IsLocS (rep σ).S s τ) :
    _root_.GlobalTheory.RowPar.weilDeligneParameterOfLocalDatum hL D rep p = hs ▸ _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 s.w) (GlobalTheory.LocLanglands.cls τ) := by
  obtain ⟨⟨s0, τ0⟩, hw, hl⟩ := p
  subst hs
  obtain rfl := splitPlace_eq_of_isLocS _ _ s s0 hw τ τ0 hτ hl
  show _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 _) (GlobalTheory.LocLanglands.cls τ0) =
    _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 _) (GlobalTheory.LocLanglands.cls τ)
  rw [show GlobalTheory.LocLanglands.cls τ0 = GlobalTheory.LocLanglands.cls τ from
    congrArg (Sigma.mk _) (cl_eq_of_isLocS (rep σ) _ τ0 τ hl hτ)]
theorem parameter_at_place_eq_reciprocity_of_local_component (σ : D.what₂.FT) (s : SplitPlace D.host.E) (τ : IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E)))
    (hτ : IsLocS (rep σ).S s τ) :
    _root_.GlobalTheory.RowPar.weilDeligneParameterAtPlace hL D rep σ s.w = _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 s.w) (GlobalTheory.LocLanglands.cls τ) := by
  classical
  have h : Nonempty (LocAt D rep σ s.w) := ⟨⟨⟨s, τ⟩, rfl, hτ⟩⟩
  unfold _root_.GlobalTheory.RowPar.weilDeligneParameterAtPlace
  rw [dite_eq_left h]
  exact _root_.GlobalTheory.RowPar.parameter_of_local_datum_eq_reciprocity hL D rep _ s rfl τ hτ
theorem dim_parameter_at_place_eq_rank (σ : D.what₂.FT) (w : PlE D.host) : (_root_.GlobalTheory.RowPar.weilDeligneParameterAtPlace hL D rep σ w).lpDim = D.R.r := by
  classical
  unfold _root_.GlobalTheory.RowPar.weilDeligneParameterAtPlace
  by_cases h : Nonempty (LocAt D rep σ w)
  · rw [dite_eq_left h]
    generalize h.some = p
    obtain ⟨⟨s0, τ0⟩, hw, hl⟩ := p
    subst hw
    exact _root_.GlobalTheory.RowPar.lpDim_locRec_alt hL _ τ0
  · rw [dite_eq_right h]
    exact (unrW D).dim σ w
end Loc
end GlobalTheory.RowPar
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MRowTame

section

@[expose] public section



section
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.RowPar
section Sat
open Formalism.UG GlobalTheory.SatInd
end Sat
section Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.SmGL GlobalTheory.LocLanglands
theorem tame_reciprocity_of_fixed_ne_bot {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (h : IsPlaceOver A w) {n : ℕ}
    (τ : IrrRep (GL (Fin n) (w.adicCompletion E)))
    (hf : GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.SplitWeil.KOne (w.adicCompletion E) (Fin n)) ≠ ⊥)
    (hq : UpperTheory.One.M.IsQg (w.adicCompletion E)) :
    (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h (cls τ)).tame := by
  obtain ⟨a, ha, ε, H⟩ := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h)
  have hx : GlobalTheory.PRep.fixed (cls τ).rep (GlobalTheory.SplitWeil.KOne (w.adicCompletion E) (Fin (cls τ).1)) ≠ ⊥ :=
    GlobalTheory.LocLanglands.fixed_ne_bot_of_equiv (IrrRep.nonempty_equiv_rep τ).some.symm hf
  obtain ⟨m, b, hb, hw⟩ := haveI := UpperTheory.One.M.charZero_compl w; _root_.UpperTheory.One.M.LawsM.depth H _ (UpperTheory.One.M.good_of_fixed hq _ hx) hx
  rw [← hb, GlobalTheory.WeilDeligne.WD.tame_mk]
  intro g hg
  refine hw g ⟨GlobalTheory.WeilDeligne.Wild_le_Ine hg, fun x hx0 => ?_⟩
  have h1 := hg x hx0
  have e : ((g : G E Ω) x - x) = ((g : G E Ω) x / x - 1) * x := by field_simp
  rw [e, map_mul]
  have h2 : (0 : _) < A.valuation x := by
    rw [pos_iff_ne_zero]; exact (Valuation.ne_zero_iff _).2 hx0
  calc A.valuation ((g : G E Ω) x / x - 1) * A.valuation x < 1 * A.valuation x := by
        exact mul_lt_mul_of_pos_right h1 h2
    _ = A.valuation x := one_mul _
end Loc
end GlobalTheory.RowPar
end
end
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.RowPar
section Sat
open Formalism.UG GlobalTheory.SatInd
end Sat
section Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.SmGL GlobalTheory.LocLanglands
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
theorem tame_parameter_at_place_of_fixed_ne_bot (σ : D.what₂.FT) (s : SplitPlace D.host.E) (τ : IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E)))
    (hτ : IsLocS (rep σ).S s τ)
    (hf : GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.SplitWeil.KOne (s.w.adicCompletion D.host.E) (Fin D.R.r)) ≠ ⊥)
    (hq : UpperTheory.One.M.IsQg (s.w.adicCompletion D.host.E)) :
    (_root_.GlobalTheory.RowPar.weilDeligneParameterAtPlace hL D rep σ s.w).tame := by
  rw [_root_.GlobalTheory.RowPar.parameter_at_place_eq_reciprocity_of_local_component hL D rep σ s τ hτ]
  exact _root_.GlobalTheory.RowPar.tame_reciprocity_of_fixed_ne_bot hL _ τ hf hq
end Loc
end GlobalTheory.RowPar
end
end
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.RowPar
section Sat
open Formalism.UG GlobalTheory.SatInd
end Sat
section Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.SmGL GlobalTheory.LocLanglands
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
end Loc
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
theorem exists_rowWD_rowTrue_m_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r), RowDepth D rep →
    ∃ Rw : RowWD D, _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep Rw.par Rw.sat := by
  intro hL D rep hD
  refine ⟨⟨_root_.GlobalTheory.RowPar.weilDeligneParameterAtPlace hL D rep, fun σ => satOf (rep σ).S, _root_.GlobalTheory.RowPar.dim_parameter_at_place_eq_rank hL D rep, fun σ k v => ?_⟩, ?_, ?_⟩
  · obtain ⟨s, τ, hs, hl, hf⟩ := hD σ k v
    obtain ⟨I⟩ := GlobalTheory.TypeRec.Model.nonempty_ident D
    have hq : UpperTheory.One.M.IsQg ((D.naut.plGw k v).adicCompletion D.host.E) := ⟨_, ⟨D.host.g_prime k⟩, I.i k v, I.cont k v⟩
    rw [← hs] at hq ⊢
    exact _root_.GlobalTheory.RowPar.tame_parameter_at_place_of_fixed_ne_bot hL D rep σ s τ hl hf hq
  · intro σ s τ hτ
    exact _root_.GlobalTheory.RowPar.parameter_at_place_eq_reciprocity_of_local_component hL D rep σ s τ hτ
  · intro σ v w hO Dv hα
    exact satOf_spec (rep σ).S v w hO Dv hα
end GlobalTheory.RowPar
end
end
end
end
end
