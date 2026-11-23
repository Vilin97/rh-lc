module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.ComplexBaseChangeOfLiterature
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CycCOfCyclic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.StrongMultOneReal
public import Development.AutomorphicArithmetic.Foundations.Convolution.Cbcc
import Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity
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
public import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PBasic
public import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.SConjSpaceC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedFactorEqProductAbove
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentsThetaPull
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
public import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSConjSatR
import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSConjSpaceC
public import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSConjSpaceR
public import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSNormPow
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.P_SSatEx

-- Source module: PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSConjSatC

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep

namespace UpperTheory.CBC.SConjSatCAux

theorem hasSatGL_of_linEquiv {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {ρ' : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}
    (T : V ≃ₗ[ℂ] W) (hf : ∀ g y, T.toLinearMap (ρ g y) = ρ' g (T.toLinearMap y)) {B : Multiset ℂˣ}
    (hB : GlobalTheory.LFun.HasSatGL w ρ B) : GlobalTheory.LFun.HasSatGL w ρ' B := by
  constructor
  · obtain ⟨x, hx⟩ := hB.exists_vec
    have h1 := hx.map T.toLinearMap hf ((map_ne_zero_iff T T.injective).2 hx.1)
    exact (Submodule.ne_bot_iff _).2 ⟨_, h1.2.1, h1.1⟩
  · intro y hy h0
    obtain ⟨x, rfl⟩ := T.surjective y
    refine (hB.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => T.injective ?_) fun e => h0 (by rw [e, map_zero])).map
      T.toLinearMap hf h0
    exact (hf k x).trans (GlobalTheory.LGrp.mem_fixed.1 hy k hk)

theorem conjSrc_conjSrc_symm {E : Type} [Field E] [NumberField E] (c : E ≃+* E) (w : HeightOneSpectrum (𝓞 E)) :
    conjSrc c (conjSrc c.symm w) = w := by
  refine (eq_conjSrc ((GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).2 ?_)).symm
  rw [(GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc c.symm w)]
  ext x
  rw [Ideal.mem_comap, Ideal.mem_comap]
  have e : (RingOfIntegers.mapRingEquiv c.symm) ((RingOfIntegers.mapRingEquiv c) x) = x := by
    ext
    simp
  rw [e]

variable {M : Type} [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M]

theorem pInf_s_sFin (s : Ad M ≃+* Ad M) (hs : Continuous s) (y : Af M) : pInf M (s (sFin M y)) = 0 := by
  let f : Af M →+ Cinf M :=
    { toFun := fun y => pInf M (s (sFin M y))
      map_zero' := by simp
      map_add' := fun a b => by simp [map_add (f := _)] }
  have hf : Continuous f := by
    have h1 : Continuous fun y : Af M => (sFin M y : Ad M) :=
      (continuous_const.prodMk continuous_id : Continuous fun y : Af M => ((0 : InfiniteAdeleRing M), y))
    show Continuous fun y : Af M => pInf M (s (sFin M y))
    exact (GlobalTheory.CuspRep.ContAut.continuous_pInf (E := M)).comp (hs.comp h1)
  have hint : ∀ z ∈ GlobalTheory.SchADecomp.intA M, f z = 0 := by
    intro z hz
    funext τ
    obtain ⟨C, hC⟩ := (GlobalTheory.SchADecomp.isCompact_intA (F := M)).exists_bound_of_continuousOn
      ((continuous_apply τ).comp hf).continuousOn
    by_contra h0
    have hpos : 0 < ‖f z τ‖ := norm_pos_iff.2 h0
    obtain ⟨m, hm⟩ := exists_nat_gt (C / ‖f z τ‖)
    have h2 := hC (m • z) (AddSubgroup.nsmul_mem _ hz m)
    rw [Function.comp_apply, map_nsmul, Pi.smul_apply, nsmul_eq_mul, norm_mul, Complex.norm_natCast] at h2
    rw [div_lt_iff₀ hpos] at hm
    linarith
  obtain ⟨N, hN, hNy⟩ := GlobalTheory.WeilM.exists_nat_mul_integral_of_isCompact M (κ := Unit)
    (isCompact_singleton (x := fun _ : Unit => y))
  have hmem : (N : Af M) * y ∈ GlobalTheory.SchADecomp.intA M := fun v => hNy _ (Set.mem_singleton _) () v
  have h3 := hint _ hmem
  rw [← nsmul_eq_mul, map_nsmul] at h3
  show f y = 0
  funext τ
  have h4 := congrFun h3 τ
  rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul] at h4
  exact (mul_eq_zero.1 h4).resolve_left (by exact_mod_cast hN.ne')

theorem s_sFin (σ : M ≃+* M) (s : Ad M ≃+* Ad M) (hs : IsGalAd σ s) (y : Af M) :
    s (sFin M y) = sFin M (conjFin σ y) := by
  refine ad_ext ?_ ?_
  · rw [pInf_s_sFin s hs.1]
    exact (map_zero (infEq M).symm).symm
  · exact hs.2.2 _

theorem map_finGL (σ : M ≃+* M) (s : Ad M ≃+* Ad M) (hs : IsGalAd σ s) {n : ℕ} (k : GL (Fin n) (Af M)) :
    Matrix.GeneralLinearGroup.map s.toRingHom (finGL M n k) =
      finGL M n (Matrix.GeneralLinearGroup.map (conjFin σ) k) := by
  ext i j
  change s ((1 : Matrix (Fin n) (Fin n) (Ad M)) i j - sFin M ((1 : Matrix (Fin n) (Fin n) (Af M)) i j) +
      sFin M (k.1 i j)) = (1 : Matrix (Fin n) (Fin n) (Ad M)) i j -
      sFin M ((1 : Matrix (Fin n) (Fin n) (Af M)) i j) + sFin M (conjFin σ (k.1 i j))
  have e1 : s ((1 : Matrix (Fin n) (Fin n) (Ad M)) i j) = (1 : Matrix (Fin n) (Fin n) (Ad M)) i j := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have e2 : conjFin σ ((1 : Matrix (Fin n) (Fin n) (Af M)) i j) = (1 : Matrix (Fin n) (Fin n) (Af M)) i j := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  rw [map_add (f := _), map_sub, e1, s_sFin σ s hs, s_sFin σ s hs, e2]

theorem main (σ : M ≃+* M) (s : Ad M ≃+* Ad M) (hs : IsGalAd σ s) {n : ℕ} (P P' : CuspSub M n)
    (hsp : (Cusp.cx P').space =
      (fun f : GA M n → ℂ => fun g => f (Matrix.GeneralLinearGroup.map s.toRingHom g)) '' (Cusp.cx P).space)
    (v : HeightOneSpectrum (𝓞 M)) {B : Multiset ℂˣ} (hB : GlobalTheory.LFun.HasSatGL v (P.locRep v) B) :
    GlobalTheory.LFun.HasSatGL (conjSrc σ v) (P'.locRep (conjSrc σ v)) B := by
  set S : GA M n →* GA M n := Matrix.GeneralLinearGroup.map s.toRingHom with hS
  have hSs : ∀ g, S (Matrix.GeneralLinearGroup.map s.symm.toRingHom g) = g := fun g => by
    ext i j
    exact s.apply_symm_apply _
  have hfwd : ∀ φ : Sm M n, φ ∈ P.V → ∃ ψ : Sm M n, ψ ∈ P'.V ∧ (fun g => φ.1 (S g)) = ψ.1 := fun φ hφ => by
    have h : (fun g => φ.1 (S g)) ∈ (Cusp.cx P').space := hsp ▸ ⟨φ.1, ⟨φ, hφ, rfl⟩, rfl⟩
    obtain ⟨ψ, hψ, e⟩ := h
    exact ⟨ψ, hψ, e⟩
  have hbwd : ∀ ψ : Sm M n, ψ ∈ P'.V → ∃ φ : Sm M n, φ ∈ P.V ∧ ψ.1 = fun g => φ.1 (S g) := fun ψ hψ => by
    have h : ψ.1 ∈ (Cusp.cx P').space := ⟨ψ, hψ, rfl⟩
    rw [hsp] at h
    obtain ⟨f, ⟨φ, hφ, rfl⟩, e⟩ := h
    exact ⟨φ, hφ, e.symm⟩
  have hT : ∀ φ : P.V, ∃ h : (fun g => φ.1.1 (S g)) ∈ Sm M n, (⟨_, h⟩ : Sm M n) ∈ P'.V := fun φ => by
    obtain ⟨ψ, hψ, e⟩ := hfwd φ.1 φ.2
    have h : (fun g => φ.1.1 (S g)) ∈ Sm M n := by rw [e]; exact ψ.2
    refine ⟨h, ?_⟩
    have e2 : (⟨_, h⟩ : Sm M n) = ψ := Subtype.ext e
    rw [e2]
    exact hψ
  let T : P.V →ₗ[ℂ] P'.V :=
    { toFun := fun φ => ⟨⟨_, (hT φ).1⟩, (hT φ).2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hTinj : Function.Injective T := fun φ φ' e => by
    have e1 : (fun g => φ.1.1 (S g)) = fun g => φ'.1.1 (S g) := congrArg (fun x : P'.V => x.1.1) e
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    have := congrFun e1 (Matrix.GeneralLinearGroup.map s.symm.toRingHom g)
    simpa only [hSs] using this
  have hTsurj : Function.Surjective T := fun ψ => by
    obtain ⟨φ, hφ, e⟩ := hbwd ψ.1 ψ.2
    exact ⟨⟨φ, hφ⟩, Subtype.ext (Subtype.ext e.symm)⟩
  let TE : P.V ≃ₗ[ℂ] P'.V := LinearEquiv.ofBijective T ⟨hTinj, hTsurj⟩
  have hinter : ∀ (k : GL (Fin n) ((conjSrc σ v).adicCompletion M)) (y : P.V),
      T (P.locRep v (Matrix.GeneralLinearGroup.map (conjLoc σ v) k) y) = P'.locRep (conjSrc σ v) k (T y) := by
    intro k y
    apply Subtype.ext
    apply Subtype.ext
    funext g
    rw [CuspSub.locRep_eq, CuspSub.locRep_eq]
    change y.1.1 (S g * finGL M n (locGL M n v (Matrix.GeneralLinearGroup.map (conjLoc σ v) k))) =
      y.1.1 (S (g * finGL M n (locGL M n (conjSrc σ v) k)))
    rw [map_mul, hS, map_finGL σ s hs, GlobalTheory.ConjPairLoc.conjFin_locGL]
  let ψ : (conjSrc σ v).adicCompletion M ≃+* v.adicCompletion M :=
    RingEquiv.ofBijective (conjLoc σ v) ⟨(conjLoc σ v).injective, GlobalTheory.CuspRep.ParLaws.conjLoc_surjective σ v⟩
  let ψ₀ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv M v ≃+* (conjSrc σ v).adicCompletion M := ψ.symm
  have h3 : ∀ a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv M v, Valued.v (ψ₀ a) = Valued.v a := fun a => by
    have := (conjLoc_spec σ v).2.2 (ψ₀ a)
    have e : conjLoc σ v (ψ₀ a) = a := ψ.apply_symm_apply a
    rw [e] at this
    exact this.symm
  have hq : Formalism.UG.qV M (conjSrc σ v) = Formalism.UG.qV M v := GlobalTheory.UnrEuler.ConjFac.absNorm_conjSrc σ v
  have hk : ∀ k, (GlobalTheory.LFun.SplitTie.glEquiv n ψ₀).symm k = Matrix.GeneralLinearGroup.map (conjLoc σ v) k :=
    fun k => by ext i j; rfl
  have hK := GlobalTheory.LFun.SplitTie.mem_KGL_iff (n := n) h3
  let ρ'' := (P.locRep v).comp (GlobalTheory.LFun.SplitTie.glEquiv n ψ₀).symm.toMonoidHom
  have hfix : ∀ x, x ∈ GlobalTheory.PRep.fixed ρ'' (GlobalTheory.LFun.KGL (conjSrc σ v) (n := n)) ↔
      x ∈ GlobalTheory.PRep.fixed (P.locRep v) (GlobalTheory.LFun.KGL v (n := n)) := fun x => GlobalTheory.LFun.mem_fixed_comp_symm _ hK
  have hB'' : GlobalTheory.LFun.HasSatGL (conjSrc σ v) ρ'' B := by
    refine ⟨?_, fun x hx h0 => (GlobalTheory.LFun.SplitTie.isSatVecGL_comp_symm h3 hq _ x B).2 (hB.2 x ((hfix x).1 hx) h0)⟩
    obtain ⟨x, hx⟩ := hB.exists_vec
    exact (Submodule.ne_bot_iff _).2 ⟨x, (hfix x).2 hx.2.1, hx.1⟩
  refine hasSatGL_of_linEquiv TE (fun k y => ?_) hB''
  change T (P.locRep v ((GlobalTheory.LFun.SplitTie.glEquiv n ψ₀).symm k) y) = _
  rw [hk]
  exact hinter k y

end UpperTheory.CBC.SConjSatCAux

open UpperTheory.CBC in
theorem UpperTheory.CBC.SConjSatC_holds : UpperTheory.CBC.SConjSatC := by
  intro K M _ _ _ _ _ _ σ s hs n P P' hsp
  have hc : ∀ x : K, σ.toRingEquiv.symm (algebraMap K M x) = algebraMap K M x := fun x => σ.symm.commutes x
  refine ⟨conjSrc σ.toRingEquiv.symm, conjSrc_injective _, fun w => GlobalTheory.DefU.ClassFin.under_conjSrc _ hc w,
    fun w => ?_, Filter.Eventually.of_forall fun w B hB => ?_⟩
  · have h := GlobalTheory.UnrEuler.ConjFac.absNorm_conjSrc σ.toRingEquiv.symm w
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply] at h
    exact h
  · have h := UpperTheory.CBC.SConjSatCAux.main σ.toRingEquiv s hs P P' hsp (conjSrc σ.toRingEquiv.symm w)
      ((CG.hasSat_mk _ _ _).1 hB)
    rw [UpperTheory.CBC.SConjSatCAux.conjSrc_conjSrc_symm] at h
    exact (CG.hasSat_mk _ _ _).2 h
end
end
end

-- Source module: PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSIsoSat

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain

namespace UpperTheory.CBC

theorem SIsoSat_holds : SIsoSat := by
  intro F _ _ n π π' h w B hB
  cases π with
  | cx p =>
    cases π' with
    | cx p' =>
      exact (GlobalTheory.CuspRep.CG.hasSat_mk p' w B).2
        (GlobalTheory.CuspRep.CuspSub.Iso.hasSatGL (π := p) (π' := p') h ((GlobalTheory.CuspRep.CG.hasSat_mk p w B).1 hB))
    | re p' => exact h.elim
  | re p =>
    cases π' with
    | cx p' => exact h.elim
    | re p' => exact UpperTheory.V.TR.CuspSub.Iso.hasSat (π := p) (π' := p') h hB

end UpperTheory.CBC
end
end
end

-- Source module: PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSSmo

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Published

namespace UpperTheory.CBC.SmoothnessOfSatakeParameters

theorem not_both (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)

theorem cx_smo (hJ : GlobalTheory.Published.JacquetShalikaRigidity) {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    {a : ℕ} (ha : 1 ≤ a) (π π' : CG E a)
    (hw : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, π.HasSat w B ∧ π'.HasSat w B) : π = π' := by
  obtain ⟨s, hs⟩ := hJ E Unit Unit (fun _ => a) (fun _ => a) (fun _ => π) (fun _ => π') (fun _ => ha) (fun _ => ha)
    (hw.mono fun w ⟨B, h1, h2⟩ => ⟨fun _ => B, fun _ => B, fun _ => h1, fun _ => h2, rfl⟩)
  exact eq_of_heq (Sigma.mk.inj (hs ())).2

end UpperTheory.CBC.SmoothnessOfSatakeParameters
end
end
end

-- Source module: PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSTwSat

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Published

theorem UpperTheory.CBC.STwSat_holds : UpperTheory.CBC.STwSat := by
  intro F _ _ n π η
  filter_upwards [(GlobalTheory.Mem.UnrAe.finite_ramified η).compl_mem_cofinite] with v hv
  have hu : η.UnrAt v := not_not.mp hv
  refine ⟨hu, fun B hB => ?_⟩
  cases π with
  | cx π => exact GlobalTheory.SphGal.hasSatGL_twist F n π η v B hu hB
  | re π => exact UpperTheory.V.TR.CuspSub.HasSat.twist hB hu
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CycFree

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.CBC

namespace UpperTheory.V.Z.Bc

private theorem smo0 (hJ : GlobalTheory.Published.JacquetShalikaRigidity) (F : Type) [Field F] [NumberField F] (n : ℕ) (hn : 1 ≤ n) (π π' : Cusp F n)
    (h : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, π.sat v B ∧ π'.sat v B) : π.Iso π' := by
  cases π with
  | cx P =>
    cases π' with
    | cx P' =>
      exact Quotient.exact (UpperTheory.CBC.SmoothnessOfSatakeParameters.cx_smo hJ hn (CG.mk P) (CG.mk P') h)
    | re P' =>
      exact (UpperTheory.CBC.SmoothnessOfSatakeParameters.not_both F ‹IsTotallyReal F› ‹IsTotallyComplex F›).elim
  | re P =>
    cases π' with
    | cx P' =>
      exact (UpperTheory.CBC.SmoothnessOfSatakeParameters.not_both F ‹IsTotallyReal F› ‹IsTotallyComplex F›).elim
    | re P' =>
      exact UpperTheory.V.Af.strongMultOneReal F n hn P P' h

private theorem conjIso0 (hJ : GlobalTheory.Published.JacquetShalikaRigidity) (h8 : SConjSpaceC) (h9 : SConjSpaceR)
    (h10 : SConjSatC) (h11 : SConjSatR) {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    {n : ℕ} (hn : 1 ≤ n) (P : Cusp M n) (σ : M ≃ₐ[K] M)
    (H : ∀ g : HeightOneSpectrum (𝓞 M) → HeightOneSpectrum (𝓞 M), Function.Injective g →
      (∀ w, (g w).under (𝓞 K) = w.under (𝓞 K)) → (∀ w, normV (g w) = normV w) →
      ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ∃ B, P.sat w B ∧ P.sat (g w) B) :
    P.ConjIso σ.toRingEquiv := by
  intro s hs
  have key : ∃ P' : Cusp M n,
      P'.space = (fun f : GA M n → ℂ => fun g => f (Matrix.GeneralLinearGroup.map s.toRingHom g)) '' P.space ∧
      ∃ g : HeightOneSpectrum (𝓞 M) → HeightOneSpectrum (𝓞 M), Function.Injective g ∧ (∀ w, (g w).under (𝓞 K) = w.under (𝓞 K)) ∧
        (∀ w, normV (g w) = normV w) ∧ ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ∀ B, P.sat (g w) B → P'.sat w B := by
    cases P with
    | cx P =>
      obtain ⟨P', hP'⟩ := h8 M σ.toRingEquiv s hs n P
      exact ⟨.cx P', hP', h10 K M σ s hs n P P' hP'⟩
    | re P =>
      obtain ⟨P', hP'⟩ := h9 M σ.toRingEquiv s hs n P
      exact ⟨.re P', hP', h11 K M σ s hs n P P' hP'⟩
  obtain ⟨P', hsp, g, hinj, hund, hnorm, hsat⟩ := key
  refine ⟨P', hsp, smo0 hJ M n hn P' P ?_⟩
  filter_upwards [hsat, H g hinj hund hnorm] with w hB ⟨B, hB1, hB2⟩
  exact ⟨B, hB _ hB2, hB1⟩

theorem cycC_of_fin_js (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hJ : GlobalTheory.Published.JacquetShalikaRigidity) (L : CBCr) : CycC := by
  intro K M _ _ _ _ _ _ hp hK n hn
  obtain ⟨L1, L2, L3⟩ := L K M hp hK n hn
  have hc := fun (P : Cusp M n) (σ : M ≃ₐ[K] M) => conjIso0 hJ SConjSpaceC_holds SConjSpaceR_holds
    SConjSatC_holds SConjSatR_holds hn P σ
  refine ⟨?_, ?_, ?_⟩
  · intro sat inf h hr
    obtain ⟨π, rfl, rfl⟩ := SCuspOf_holds K n sat inf h
    rcases L1 π hr with ⟨η, hη, hi⟩ | ⟨P, hw, hinf⟩
    · refine Or.inl ⟨η, hη, ?_⟩
      filter_upwards [STwSat_holds K n π η, SatakeParameterExistence.of_fin hF K n π] with v ⟨hu, ht⟩ ⟨B, hB⟩
      exact ⟨hu, B, hB, SSatUniq_holds K n π v _ _ (SIsoSat_holds K n _ _ hi v _ (ht B hB)) hB⟩
    · exact Or.inr ⟨P.sat, P.inf, SIsCusp_holds M n P, hw, hinf⟩
  · intro sat' inf' h hr hinv
    obtain ⟨P, rfl, rfl⟩ := SCuspOf_holds M n sat' inf' h
    refine (fun ⟨π, hw, hinf⟩ => ⟨π.sat, π.inf, SIsCusp_holds K n π, hw, hinf⟩) (L2 P hr fun σ => hc P σ fun g _ hund _ => ?_)
    filter_upwards [hinv] with w hall
    exact hall (g w) (hund w)
  · intro sat inf sat' inf' h h' hw sat₁ inf₁ h₁ hw₁
    obtain ⟨π, rfl, rfl⟩ := SCuspOf_holds K n sat inf h
    obtain ⟨P, rfl, rfl⟩ := SCuspOf_holds M n sat' inf' h'
    obtain ⟨π₁, rfl, rfl⟩ := SCuspOf_holds K n sat₁ inf₁ h₁
    obtain ⟨η, hη, hi⟩ := L3 π P (fun σ => hc P σ fun g hinj hund hnorm => by
      filter_upwards [hw, hinj.tendsto_cofinite.eventually hw] with w h1' h2'
      obtain ⟨f, hf⟩ := SNormPow_holds K M w
      obtain ⟨B, hB, hPB⟩ := h1' f hf
      obtain ⟨B', hB', hPB'⟩ := h2' f (by rw [hnorm w, hund w]; exact hf)
      rw [hund w] at hB'
      obtain rfl := SSatUniq_holds K n π _ _ _ hB hB'
      exact ⟨_, hPB, hPB'⟩) hw π₁ hw₁
    refine ⟨η, hη, ?_⟩
    filter_upwards [STwSat_holds K n π η, SatakeParameterExistence.of_fin hF K n π] with v ⟨hu, ht⟩ ⟨B, hB⟩
    exact ⟨hu, B, hB, SIsoSat_holds K n _ _ hi v _ (ht B hB)⟩

theorem cycC_holds : CycC :=
  cycC_of_fin_js CuspFormAutomorphicBounds.automorphicFormsFiniteGL PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity (cbcr_of_cbcc UpperTheory.ConvolutionTheory.cbcc)

end UpperTheory.V.Z.Bc
end
end
end
