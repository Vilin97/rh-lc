module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulVecEqPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSlotsGlobal
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CyclotomicFrobeniusPowerSeriesXEqMulQuotient
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffExpSub
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BoundedOnFramesIffIntegralOnFrames
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWachModuleMapMatrixReductionComm
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableLatticeChainWithLinesMatrixForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete
import Formalism.PieriBlockIdeals.PieriColumnMinors.HeckeLFunctionIdealEulerProduct
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitRootCyclotomicExpExpansions

section

@[expose] public section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

namespace GlobalTheory.WachExp

theorem exists_locExp_expAt : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), l ≠ 2 → (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) → ∃ (u : ℤ_[l]ˣ) (c : ℤ_[l]) (ζ : ↥(OL LL)) (jj : ℕ → PowerSeries ↥(OL LL) →+* PowerSeries ↥LL.1), (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c ∧ IsUnit c ∧ IsPrimitiveRoot ζ l ∧ ζ - 1 ∈ maximalIdeal ↥(OL LL) ∧ ∀ b ∈ Finset.Ioo 0 l, IsLocExp l ↥(OL LL) ↥LL.1 (OL LL).val.toRingHom (ζ ^ b - 1) (u : ℤ_[l]) (jj b) ∧ IsExpAt (OL LL).val.toRingHom (ζ ^ b) (jj b) := by
  intro l _ LL _ hex
  obtain ⟨ζL, hζL⟩ := hex
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hfin := LL.2
  have hint : IsIntegral ℤ_[l] ζL := IsIntegral.of_pow hl (by rw [hζL.pow_eq_one]; exact isIntegral_one)
  let ζ : ↥(OL LL) := ⟨ζL, hint⟩
  have hζ : IsPrimitiveRoot ζ l :=
    IsPrimitiveRoot.of_map_of_injective (f := (OL LL).val) hζL Subtype.val_injective

  have hu : IsUnit (1 + (l : ℤ_[l]) * 1) := by
    have h := IsLocalRing.isUnit_or_isUnit_one_sub_self (-(l : ℤ_[l]))
    rcases h with h | h
    · exact absurd ((IsUnit.neg_iff _).1 h) PadicInt.prime_p.not_isUnit
    · simpa [sub_eq_add_neg] using h
  let u : ℤ_[l]ˣ := hu.unit
  have hu1 : (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * 1 := hu.unit_spec

  have hmax : ζ - 1 ∈ maximalIdeal ↥(OL LL) := by
    refine (GlobalTheory.DiscEval.mem_maximalIdeal_iff_norm (p := l) LL.1 _).2 ?_
    refine lt_of_eq_of_lt (b := ‖((((ζL - 1 : ↥LL.1)) : PadicAlgCl l) : ℂ_[l])‖) rfl ?_
    rw [PadicComplex.norm_extends]
    exact norm_root_sub_one_lt LL hζL.pow_eq_one
  have hpow : ∀ b : ℕ, (ζL ^ b) ^ l = 1 := fun b => by
    rw [← pow_mul, mul_comm, pow_mul, hζL.pow_eq_one, one_pow]
  choose ev hC hev using fun b : ℕ => exists_ev LL (ζL ^ b) (hpow b)
  refine ⟨u, 1, ζ, ev, hu1, isUnit_one, hζ, hmax, fun b _ => ⟨⟨fun a => hC b a, ?_, fun f => ?_⟩, ⟨fun a => hC b a, hev b⟩⟩⟩
  · obtain ⟨g, hg⟩ : X ∣ exp ↥LL.1 - 1 := X_dvd_iff.2 (by simp)
    have hg0 : constantCoeff g = 1 := by
      have h := congrArg (coeff 1) hg
      rw [coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply] at h
      rw [← h]; simp [coeff_exp]
    have hzb : ζL ^ b ≠ 0 := pow_ne_zero _ (hζL.ne_zero (by omega))
    have hunit : IsUnit (C (ζL ^ b) * g) := by
      rw [PowerSeries.isUnit_iff_constantCoeff]; simp [hg0, hzb]
    have hcalc : ev b (X - C (ζ ^ b - 1)) = X * (C (ζL ^ b) * g) := by
      rw [map_sub, hev, hC]
      have hco : ((ζ ^ b - 1 : ↥(OL LL)) : ↥LL.1) = ζL ^ b - 1 := rfl
      rw [hco, map_sub (C : ↥LL.1 →+* _), map_one]
      linear_combination (C (ζL ^ b)) * hg
    rw [hcalc]
    exact associated_mul_unit_left X _ hunit
  · set r : ↥LL.1 := algebraMap ℤ_[l] ↥LL.1 (u : ℤ_[l]) with hr_def
    have hact : Formalism.CohomologicalDescent.HeightDescentMinors.act l ↥(OL LL) (u : ℤ_[l]) f = GlobalTheory.Fon.gam ↥(OL LL) (u : ℤ_[l]) f := by
      simp only [Formalism.CohomologicalDescent.HeightDescentMinors.act, Formalism.CohomologicalDescent.HeightDescentMinors.br, GlobalTheory.Fon.gam]
      exact (congrFun (coe_substAlgHom _) f).symm
    have hxz := ringHom_gam_X (O := ↥(OL LL)) (L := ↥LL.1) (ev b) (hC b) (ζL ^ b) (hev b) (hpow b)
      (u : ℤ_[l]) ⟨1, by rw [hu1]; ring⟩
    have huniq := ev_unique LL (C (ζL ^ b) * rescale r (exp ↥LL.1) - 1)
      (by rw [constantCoeff_exp_sub]; exact norm_root_sub_one_lt LL (hpow b))
      ((ev b).comp (GlobalTheory.Fon.gam ↥(OL LL) (u : ℤ_[l]) : PowerSeries ↥(OL LL) →+* PowerSeries ↥(OL LL)))
      ((rescale r).comp (ev b))
      (fun a => by
        change ev b (GlobalTheory.Fon.gam ↥(OL LL) (u : ℤ_[l]) (C a)) = _
        rw [GlobalTheory.Fon.gam_C, hC])
      (fun a => by
        change rescale r (ev b (C a)) = _
        rw [hC, rescale_C'])
      hxz
      (by
        change rescale r (ev b X) = _
        rw [hev, map_sub, map_mul, map_one, rescale_C'])
    rw [hact]
    exact RingHom.congr_fun huniq f

end GlobalTheory.WachExp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitRootCyclotomicExpExpansionsStatement

section

@[expose] public section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

theorem _root_.GlobalTheory.T.exists_unit_root_cyclotomicExpExpansions : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), l ≠ 2 → (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) → ∃ (u : ℤ_[l]ˣ) (c : ℤ_[l]) (ζ : ↥(OL LL)) (jj : ℕ → PowerSeries ↥(OL LL) →+* PowerSeries ↥LL.1), (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c ∧ IsUnit c ∧ IsPrimitiveRoot ζ l ∧ ζ - 1 ∈ maximalIdeal ↥(OL LL) ∧ ∀ b ∈ Finset.Ioo 0 l, IsLocExp l ↥(OL LL) ↥LL.1 (OL LL).val.toRingHom (ζ ^ b - 1) (u : ℤ_[l]) (jj b) ∧ IsExpAt (OL LL).val.toRingHom (ζ ^ b) (jj b) := by
  first | exact @GlobalTheory.WachExp.exists_locExp_expAt | exact GlobalTheory.WachExp.exists_locExp_expAt | (intros; apply GlobalTheory.WachExp.exists_locExp_expAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableLatticeChainWithLinesMatrixFormStatement

section

@[expose] public section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

theorem _root_.GlobalTheory.T.stable_lattice_chain_with_lines_matrix_form : ∀ (Γ O : Type) [Group Γ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n t R : ℕ) (r : Γ →* GL (Fin n) O) (ψ : Fin t → Γ →* Oˣ) (ϖ : O) (M : Fin (R + 1) → Submodule O (Fin n → O)) (rs : Fin t → Fin R), Irreducible ϖ → (∀ x, x ∈ M 0 ↔ ∃ y : Fin n → O, x = fun a => ϖ * y a) → M (Fin.last R) = ⊤ → Monotone M → (∀ g k x, x ∈ M k → (r g : Matrix (Fin n) (Fin n) O).mulVec x ∈ M k) → (∀ s, ∃ x ∈ M (rs s).succ, x ∉ M (rs s).castSucc ∧ M (rs s).succ = M (rs s).castSucc ⊔ Submodule.span O {x} ∧ ∀ g, (r g : Matrix (Fin n) (Fin n) O).mulVec x - (fun a => ((ψ s g : Oˣ) : O) * x a) ∈ M (rs s).castSucc) → ∃ (x : GalMats Γ O n t R) (dim : Fin (R + 1) → ℕ), x.Chain (residue O) r (fun s => GlobalTheory.TripleGal.rk1 (ψ s)) rs dim ∧ dim 0 = 0 ∧ dim (Fin.last R) = n ∧ ∀ s, dim (rs s).succ = dim (rs s).castSucc + 1 := by
  first | exact @GlobalTheory.WachChain.chain_of_lattices | exact GlobalTheory.WachChain.chain_of_lattices | (intros; apply GlobalTheory.WachChain.chain_of_lattices <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WachLatticesRankOneModelsReducedFiltration

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

private theorem lau_eq_vecL {F : Type} [Field F] {n : ℕ} (y : Fin n → F⟦X⟧) :
    GlobalTheory.WachBlock.lau y = GlobalTheory.WachPlace.vecL y := by
  funext a
  rfl

private theorem unConst : UnConst := by
  exact unit_series_constant_holds

private theorem lau_mem_iff_vecL_mem {F : Type} [Field F] {n : ℕ}
    {S : Submodule (LaurentSeries F) (Fin n → LaurentSeries F)} {y : Fin n → F⟦X⟧} :
    GlobalTheory.WachBlock.lau y ∈ S ↔ GlobalTheory.WachPlace.vecL y ∈ S := by
  rw [lau_eq_vecL]

private theorem map_comp_rk1_eq_rk1_map {Γ : Type} [Group Γ] {l : ℕ} [Fact l.Prime] (LL : FinExt l)
    (χ : Γ →* (↥(OL LL))ˣ) :
    (Matrix.GeneralLinearGroup.map (toOm LL)).comp (GlobalTheory.TripleGal.rk1 χ) =
      GlobalTheory.TripleGal.rk1 ((Units.map (GlobalTheory.WachBlock.ofOL l LL).toMonoidHom).comp χ) := by
  ext g i j
  simp [GlobalTheory.TripleGal.rk1, toOm, GlobalTheory.WachBlock.ofOL]
  obtain rfl := Subsingleton.elim i j
  simp


open NumberField GlobalTheory.ExpFrame in
theorem GlobalTheory.WachPlace.wach_lattices : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (σ : Equiv.Perm (E →+* PadicAlgCl l)), IsFrobPerm σ → ∀ (n t h : ℕ) (J : (E →+* PadicAlgCl l) → Fin n → ℤ) (bot : (E →+* PadicAlgCl l) → ℤ), (∀ i a, 0 ≤ J i a ∧ J i a ≤ h) → (∀ i (s : Fin t), 0 ≤ bot i + ((s : ℕ) : ℤ) ∧ bot i + ((s : ℕ) : ℤ) ≤ h) → GlobalTheory.WachBlock.IntegralBlock E Ω l n t J bot → ∃ (O' F L' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : Algebra ℤ_[l] O') (_ : Field F) (_ : CharP F l) (_ : Field L') (I : Ideal O') (_ : IsAdicComplete I O') (red : O' →+* F) (un : PowerSeries O') (N : Formalism.CohomologicalDescent.FrobeniusPeriodChange.Lat (E →+* PadicAlgCl l) n O') (Npsi : Fin t → Formalism.CohomologicalDescent.FrobeniusPeriodChange.Lat (E →+* PadicAlgCl l) 1 O') (u : ℤ_[l]ˣ) (c : ℤ_[l]) (ζ : O') (em : O' →+* L') (jj : ℕ → PowerSeries O' →+* PowerSeries L'), ((u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c ∧ IsUnit c ∧ Formalism.CohomologicalDescent.FrobeniusPeriodChange.IsUn l O' (u : ℤ_[l]) un) ∧ (IsPrimitiveRoot ζ l ∧ ζ - 1 ∈ I ∧ Function.Injective em ∧ ∀ b ∈ Finset.Ioo 0 l, Formalism.CohomologicalDescent.FrobeniusPeriodChange.IsLocExp l O' L' em (ζ ^ b - 1) (u : ℤ_[l]) (jj b)) ∧ Formalism.CohomologicalDescent.FrobeniusPeriodChange.LatN l N h u J em jj ∧ (∀ s, Formalism.CohomologicalDescent.FrobeniusPeriodChange.LatN l (Npsi s) h u (fun i _ => bot i + ((s : ℕ) : ℤ)) em jj) ∧ GlobalTheory.WachBlock.RedFilt σ l (PowerSeries.map red un) (fun i => (N.P i).map (PowerSeries.map red)) (fun i => (N.D i).map (PowerSeries.map red)) (fun s i => PowerSeries.map red ((Npsi s).P i 0 0)) (fun s i => PowerSeries.map red ((Npsi s).D i 0 0)) := by
  intro hBS E Ω _ _ _ _ _ _ l _ hl hd σ hσ n t h J bot hJ hbot hIB
  obtain ⟨LL, r, ψ, ϖ, R, M, rs, hz, hE, hcr, hψcr, hirr, hM0, hMtop, hmono, hstab, hrs, hlines⟩ := hIB
  obtain ⟨_, _, _⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  haveI : CharP (ResidueField ↥(OL LL)) l := GlobalTheory.WachMap.charP_residueField_of_irreducible LL
  obtain ⟨x, dim, hx, hd0, hdR, hds⟩ :=
    GlobalTheory.T.stable_lattice_chain_with_lines_matrix_form _ ↥(OL LL) n t R r ψ ϖ M rs hirr hM0 hMtop hmono hstab hlines
  obtain ⟨u, c, ζ, jj, hu, hc, hζ, hζm, hjj⟩ := GlobalTheory.T.exists_unit_root_cyclotomicExpExpansions l LL hl hz
  obtain ⟨un, hun⟩ := (unConst l ↥(OL LL) hl (u : ℤ_[l]) c hu).1
  have hψ' : ∀ s, GlobalTheory.ExpFrame.CrysWith
      ((Matrix.GeneralLinearGroup.map (toOm LL)).comp (GlobalTheory.TripleGal.rk1 (ψ s)))
      fun τ => {bot τ + ((s : ℕ) : ℤ)} := by
    intro s
    rw [map_comp_rk1_eq_rk1_map]
    exact hψcr s
  obtain ⟨N, Nψ, y, hN, hNψ, hy⟩ := GlobalTheory.WachPlace.exists_positions_global hBS hl hd hσ
    (J := J) (wt := fun s i => bot i + ((s : ℕ) : ℤ)) hJ (fun s i => hbot i s) hz hE
    (r := r) (ψ := fun s => GlobalTheory.TripleGal.rk1 (ψ s)) hcr hψ' hx hu hun hζ (fun a ha => (hjj a ha).2)
  obtain ⟨V, e, m, hV0, hVrk, hVphi, hVgam, hVe, hVphie, hVgame⟩ :=
    GlobalTheory.WachPlace.filtration_of_chain σ (Fact.out : l.Prime).pos
      (PowerSeries.map (residue ↥(OL LL)) un)
      (fun i => (N.P i).map (PowerSeries.map (residue ↥(OL LL))))
      (fun i => (N.D i).map (PowerSeries.map (residue ↥(OL LL))))
      (fun s i => ((Nψ s).P i).map (PowerSeries.map (residue ↥(OL LL))))
      (fun s i => ((Nψ s).D i).map (PowerSeries.map (residue ↥(OL LL)))) rs dim y hd0 hdR hds hy
  refine ⟨↥(OL LL), ResidueField ↥(OL LL), ↥LL.1, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, maximalIdeal ↥(OL LL), inferInstance,
    residue ↥(OL LL), un, N, Nψ, u, c, ζ, (OL LL).val.toRingHom, jj, ⟨hu, hc, hun⟩,
    ⟨hζ, hζm, Subtype.val_injective, fun b hb => (hjj b hb).1⟩, hN, hNψ, ?_⟩
  unfold GlobalTheory.WachBlock.RedFilt
  refine ⟨R, V, rs, e, m, hrs, hV0, hVrk, ?_, ?_, ?_, ?_, ?_⟩
  · intro i k v hv
    exact lau_mem_iff_vecL_mem.2 (hVphi i k v (lau_mem_iff_vecL_mem.1 hv))
  · intro i k v hv
    exact lau_mem_iff_vecL_mem.2 (hVgam i k v (lau_mem_iff_vecL_mem.1 hv))
  · intro i s
    simp only [lau_eq_vecL]
    exact hVe i s
  · intro i s
    simp only [lau_eq_vecL]
    exact hVphie i s
  · intro i s
    simp only [lau_eq_vecL]
    exact hVgame i s

end
end
end
