module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GESymmApply
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.IotaSurjectiveHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ZMemPerp
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.IotaSurjectiveHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowLatticeMassHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowLatticeMassHolds
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.HermitianLattices.HermitianLatticesProofs.UnimodularSpan

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ExistsSE

section

@[expose] public section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowWeightPf

open PI.UnitaryGroupMassFormula.CntFormula.RowsMassW PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Section

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

def lpS (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Submodule (𝓞 D.host.E) (VS D).V :=
  Λ ⊓ (perpS (VS D) F0.X).restrictScalars (𝓞 D.host.E)

variable {D F0}

theorem sE_eq (Λ : Submodule (𝓞 D.host.E) (VS D).V) (ρ : lpS D F0 Λ →ₗ[𝓞 D.host.E] lpS D F0 Λ)
    (hρid : ∀ y : lpS D F0 Λ, (y : (VS D).V) ∈ F0.X → ρ y = y)
    {s : Type} [Fintype s] (c : Basis s D.host.E (WbQ D F0)) (a : s → perpS (VS D) F0.X)
    (hac : ∀ i, (Submodule.Quotient.mk (a i) : WbQ D F0) = c i)
    (y : s → lpS D F0 Λ) (hya : ∀ i, (y i : (VS D).V) = a i)
    (sE : WbQ D F0 →ₗ[D.host.E] perpS (VS D) F0.X)
    (hsEc : ∀ i, (sE (c i) : (VS D).V) = (y i : (VS D).V) - (ρ (y i) : (VS D).V))
    (b : perpS (VS D) F0.X) (yb : lpS D F0 Λ) (hyb : (yb : (VS D).V) = b)
    (d : 𝓞 D.host.E) (hd0 : d ≠ 0) (o : s → 𝓞 D.host.E)
    (ho : ∑ i, o i • c i = d • (Submodule.Quotient.mk b : WbQ D F0)) :
    (sE (Submodule.Quotient.mk b) : (VS D).V) = (b : (VS D).V) - (ρ yb : (VS D).V) := by
  have hsm : ∀ (r : 𝓞 D.host.E) (v : (VS D).V),
      r • v = (algebraMap (𝓞 D.host.E) D.host.E r) • v := fun r v => (algebraMap_smul D.host.E r v).symm
  have hq : (Submodule.Quotient.mk (∑ i, o i • a i - d • b) : WbQ D F0) = 0 := by

    rw [← Submodule.mkQ_apply, map_sub, map_sum]
    simp only [LinearMap.map_smul_of_tower, Submodule.mkQ_apply, hac, ho, sub_self]
  have hmem := (Submodule.Quotient.mk_eq_zero _).mp hq
  rw [Submodule.mem_comap] at hmem
  have hzX : ((∑ i, o i • y i - d • yb : lpS D F0 Λ) : (VS D).V) ∈ F0.X := by
    convert hmem using 1
    simp [hya, hyb]
  have hρz := hρid _ hzX
  have e := congrArg (fun u : lpS D F0 Λ => (u : (VS D).V)) hρz

  simp only [map_sub, map_sum, map_smul, Submodule.coe_sub, Submodule.coe_sum,
  Submodule.coe_smul] at e
  have h1 : ∑ i, o i • (y i : (VS D).V) - ∑ i, o i • (ρ (y i) : (VS D).V) =
      d • (yb : (VS D).V) - d • (ρ yb : (VS D).V) := by
    rw [sub_eq_sub_iff_sub_eq_sub]
    exact e.symm
  have h2 := congrArg (fun q => ((sE q : perpS (VS D) F0.X) : (VS D).V)) ho

  simp only [map_sum, LinearMap.map_smul_of_tower, Submodule.coe_sum, Submodule.coe_smul_of_tower,
  hsEc] at h2
  have hd : (algebraMap (𝓞 D.host.E) D.host.E d) ≠ 0 := by
    intro h0
    apply hd0
    exact (FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E) (h0.trans (map_zero _).symm)
  apply smul_right_injective (VS D).V hd
  simp only
  rw [← hsm, ← hsm, ← h2]
  simp only [smul_sub, Finset.sum_sub_distrib]
  rw [h1, hyb]

theorem exists_sE (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hL : Submodule.IsFullLattice D.host.E Λ) :
    ∃ sE : WbQ D F0 →ₗ[D.host.E] perpS (VS D) F0.X,
      (∀ a, (Submodule.Quotient.mk (sE a) : WbQ D F0) = a) ∧
      ∀ m ∈ Mof D F0 Λ, ((sE m : perpS (VS D) F0.X) : (VS D).V) ∈ Λ := by
  classical
  have hlpfg : (lpS D F0 Λ).FG := Submodule.FG.of_le hL.fg inf_le_left
  obtain ⟨ρ, hρX, hρid⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.exists_retract (lpS D F0 Λ) hlpfg F0.X
  have hlpP : ∀ y : lpS D F0 Λ, (y : (VS D).V) ∈ perpS (VS D) F0.X := fun y => (Submodule.mem_inf.1 y.2).2
  have hlpΛ : ∀ y : lpS D F0 Λ, (y : (VS D).V) ∈ Λ := fun y => (Submodule.mem_inf.1 y.2).1
  have hPmem : ∀ y : lpS D F0 Λ, (y : (VS D).V) - (ρ y : (VS D).V) ∈ perpS (VS D) F0.X :=
    fun y => Submodule.sub_mem _ (hlpP y) (hlpP (ρ y))
  have hPΛ : ∀ y : lpS D F0 Λ, (y : (VS D).V) - (ρ y : (VS D).V) ∈ Λ :=
    fun y => Submodule.sub_mem _ (hlpΛ y) (hlpΛ (ρ y))
  have hMlat := Mof_isLattice D F0 Λ hL.toIsLattice
  obtain ⟨s, _, c, hcv, hsM⟩ :=
    Formalism.HermitianLatticesTheory.dualLattice_basis (R := 𝓞 D.host.E) (Mof D F0 Λ)
      (Mof_span D F0 Λ hL.span_eq_top)
  have hci : ∀ i, c i ∈ Mof D F0 Λ := fun i => by rw [hcv]; exact hsM i.2
  choose a haΛ hac using fun i => (mem_Mof D F0 Λ (c i)).1 (hci i)
  let y : s → lpS D F0 Λ := fun i => ⟨(a i : (VS D).V), Submodule.mem_inf.2 ⟨haΛ i, (a i).2⟩⟩
  let sE : WbQ D F0 →ₗ[D.host.E] perpS (VS D) F0.X :=
    c.constr D.host.E (fun i => ⟨(y i : (VS D).V) - (ρ (y i) : (VS D).V), hPmem (y i)⟩)
  have hsEc : ∀ i, (sE (c i) : (VS D).V) = (y i : (VS D).V) - (ρ (y i) : (VS D).V) := by
    intro i
    simp only [sE, Basis.constr_basis]
  have hsE : ∀ b, (Submodule.Quotient.mk (sE b) : WbQ D F0) = b := by
    have hlin : (F0.X.comap (perpS (VS D) F0.X).subtype).mkQ ∘ₗ sE = LinearMap.id := by
      refine c.ext fun i => ?_
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearMap.id_coe, id_eq]
      conv_rhs => rw [← hac i]
      rw [mk_eq_mk, hsEc]
      have : (y i : (VS D).V) = (a i : (VS D).V) := rfl
      rw [this, sub_sub_cancel_left]
      exact F0.X.neg_mem (hρX (y i))
    intro b
    exact LinearMap.congr_fun hlin b
  refine ⟨sE, hsE, ?_⟩
  intro m hm
  obtain ⟨b, hbΛ, rfl⟩ := (mem_Mof D F0 Λ m).1 hm
  let yb : lpS D F0 Λ := ⟨(b : (VS D).V), Submodule.mem_inf.2 ⟨hbΛ, b.2⟩⟩
  obtain ⟨d, hd0, hdM⟩ := Formalism.HermitianLatticesTheory.dualLattice_denom c (Mof D F0 Λ) hMlat.fg
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 D.host.E)).1 (hdM _ hm)
  rw [sE_eq Λ ρ hρid c a hac y (fun i => rfl) sE hsEc b yb rfl d hd0 o ho]
  exact hPΛ yb

end Section

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowWeightPf
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.StabilizerSymmMapsOrthogonal

section

@[expose] public section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowWeightPf

open PI.UnitaryGroupMassFormula.CntFormula.RowsMassW PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem lift_span_eq_top_of_unimodular (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hL : Λ.FG) (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) :
    Submodule.span D.host.E (Λ : Set (VS D).V) = ⊤ := by
  exact Formalism.HermitianLatticesTheory.IsUnimodular.span_eq_top hU (VS D).herm hL


section Lift

variable {D : D7} {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T}
variable {sE : WbQ D F0 →ₗ[D.host.E] perpS (VS D) F0.X} {u : (VS D).V →ₗ[D.host.E] WbQ D F0}

theorem Xa_le_X (j : ℕ) : F0.Xa j ≤ F0.X :=
  Submodule.span_mono (Set.image_subset_range _ _)

theorem gF_X (hu : ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v)
    (σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0) {x : (VS D).V} (hx : x ∈ F0.X) : gF D F0 sE u σ x = x := by
  rw [gF_apply, u_X hu hx, map_zero, sub_self, map_zero, Submodule.coe_zero, add_zero]

theorem gF_perp_mk (hsE : ∀ a, (Submodule.Quotient.mk (sE a) : WbQ D F0) = a)
    (hu : ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v)
    (σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0) (y : perpS (VS D) F0.X) (h : gF D F0 sE u σ y ∈ perpS (VS D) F0.X) :
    (Submodule.Quotient.mk ⟨gF D F0 sE u σ y, h⟩ : WbQ D F0) = σ (Submodule.Quotient.mk y) := by
  have e : (⟨gF D F0 sE u σ y, h⟩ : perpS (VS D) F0.X) =
      y + sE (σ (Submodule.Quotient.mk y) - Submodule.Quotient.mk y) := by
    apply Subtype.ext
    change gF D F0 sE u σ (y : (VS D).V) = _
    rw [gF_apply, u_perp hsE hu y, Submodule.coe_add]
  rw [e, Submodule.Quotient.mk_add, hsE]
  abel

theorem quotient_lift_fixes_anisotropic (hsE : ∀ a, (Submodule.Quotient.mk (sE a) : WbQ D F0) = a)
    (hu : ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v)
    (σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0) (hz : σ (zbar D F0) = zbar D F0) : gF D F0 sE u σ F0.z = F0.z := by
  have e : u F0.z = zbar D F0 := u_perp hsE hu ⟨F0.z, z_mem_perp D F0⟩
  rw [gF_apply, e, hz, sub_self, map_zero, Submodule.coe_zero, add_zero]

theorem gF_lam (hu : ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ)
    (hsEM : ∀ m ∈ Mof D F0 Λ, ((sE m : perpS (VS D) F0.X) : (VS D).V) ∈ Λ)
    (hMu : Formalism.HermitianLatticesTheory.dual (hWb D F0) (Mof D F0 Λ) = Mof D F0 Λ)
    (σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0) (hσM : ∀ m ∈ Mof D F0 Λ, σ m ∈ Mof D F0 Λ)
    {l : (VS D).V} (hl : l ∈ Λ) : gF D F0 sE u σ l ∈ Λ := by
  have hul : u l ∈ Mof D F0 Λ := by
    rw [← hMu, Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
    intro m hm
    rw [hu]
    obtain ⟨o, ho⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.int_val (S := VS D) hU (hsEM m hm) hl
    exact Submodule.mem_one.2 ⟨o, ho⟩
  rw [gF_apply]
  exact Submodule.add_mem _ hl (hsEM _ (Submodule.sub_mem _ (hσM _ hul) hul))

theorem lift (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hL : Submodule.IsLattice D.host.E Λ)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) (σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0)
    (hσ : σ ∈ stabZ (hWb D F0) (zbar D F0) (Mof D F0 Λ)) :
    (σ : WbQ D F0 → WbQ D F0) ∈ autLz D F0 Λ := by
  obtain ⟨⟨hσi, hσz⟩, hσM⟩ := hσ
  have hfull : Submodule.IsFullLattice D.host.E Λ :=
    { toIsLattice := hL, span_eq_top := lift_span_eq_top_of_unimodular D hL.fg hU }
  obtain ⟨sE, hsE, hsEM⟩ := exists_sE (F0 := F0) Λ hfull
  obtain ⟨u, hu⟩ := exists_u D F0 sE
  have hMu : Formalism.HermitianLatticesTheory.dual (hWb D F0) (Mof D F0 Λ) = Mof D F0 Λ := Mof_unimod D F0 Λ hL hU
  have hσM1 : ∀ m ∈ Mof D F0 Λ, σ m ∈ Mof D F0 Λ := by
    intro m hm
    rw [← hσM]
    exact Submodule.mem_map_of_mem hm
  have hσM2 : ∀ m ∈ Mof D F0 Λ, σ.symm m ∈ Mof D F0 Λ := by
    intro m hm
    rw [← hσM] at hm
    obtain ⟨m', hm', rfl⟩ := hm
    simpa using hm'
  have hisom : ∀ x y, hWb D F0 (σ x) (σ y) = hWb D F0 x y := hσi
  refine ⟨gE hsE hu σ, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x y
    exact gF_isom hsE hu σ hisom x y
  · intro j
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      show gF D F0 sE u σ w ∈ F0.Xa j
      rw [gF_X hu σ (Xa_le_X j hw)]
      exact hw
    · intro hv
      refine ⟨v, hv, ?_⟩
      show gF D F0 sE u σ v = v
      exact gF_X hu σ (Xa_le_X j hv)
  · exact quotient_lift_fixes_anisotropic hsE hu σ hσz
  · apply le_antisymm
    · rintro _ ⟨l, hl, rfl⟩
      exact gF_lam hu Λ hU hsEM hMu σ hσM1 hl
    · intro l hl
      refine ⟨(gE hsE hu σ).symm l, ?_, ?_⟩
      · rw [gE_symm_apply]
        exact gF_lam hu Λ hU hsEM hMu σ.symm hσM2 hl
      · show gE hsE hu σ ((gE hsE hu σ).symm l) = l
        exact LinearEquiv.apply_symm_apply _ l
  · intro x hx
    exact (gF_perp_mk hsE hu σ x hx).symm

end Lift

section Induced

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

theorem Xa_r : F0.Xa D.R.rS = F0.X := by
  unfold FlagG.Xa FlagG.X
  congr 1
  ext v
  simp

variable {D F0}

theorem stabF_X {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) :
    F0.X.map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.X := by
  rw [← Xa_r D F0]
  exact hγ.2.1 _

theorem stabilizer_maps_isotropic {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) {x : (VS D).V} (hx : x ∈ F0.X) :
    γ x ∈ F0.X := by
  rw [← stabF_X hγ]
  exact Submodule.mem_map_of_mem hx

theorem stabilizer_symm_maps_isotropic {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) {x : (VS D).V} (hx : x ∈ F0.X) :
    γ.symm x ∈ F0.X := by
  rw [← stabF_X hγ] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  simpa using hw

theorem stabilizer_maps_orthogonal {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) {y : (VS D).V}
    (hy : y ∈ perpS (VS D) F0.X) : γ y ∈ perpS (VS D) F0.X := by
  intro x hx
  have h := hy (γ.symm x) (stabilizer_symm_maps_isotropic hγ hx)
  rw [← hγ.1 (γ.symm x) y, LinearEquiv.apply_symm_apply] at h
  exact h

theorem stabilizer_symm_maps_orthogonal {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) {y : (VS D).V}
    (hy : y ∈ perpS (VS D) F0.X) : γ.symm y ∈ perpS (VS D) F0.X := by
  intro x hx
  have h := hy (γ x) (stabilizer_maps_isotropic hγ hx)
  rw [← LinearEquiv.apply_symm_apply γ y, hγ.1] at h
  exact h

def indL (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hp : ∀ y ∈ perpS (VS D) F0.X, γ y ∈ perpS (VS D) F0.X)
    (hX : ∀ x ∈ F0.X, γ x ∈ F0.X) : WbQ D F0 →ₗ[D.host.E] WbQ D F0 :=
  Submodule.mapQ _ _ ((γ : (VS D).V →ₗ[D.host.E] (VS D).V).restrict hp) (fun x hx => hX _ hx)

theorem indL_mk (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hp : ∀ y ∈ perpS (VS D) F0.X, γ y ∈ perpS (VS D) F0.X)
    (hX : ∀ x ∈ F0.X, γ x ∈ F0.X) (a : perpS (VS D) F0.X) :
    indL γ hp hX (Submodule.Quotient.mk a) = Submodule.Quotient.mk ⟨γ a, hp a a.2⟩ := rfl

def indE {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0 :=
  LinearEquiv.ofLinear (indL γ (fun y hy => stabilizer_maps_orthogonal hγ hy) (fun x hx => stabilizer_maps_isotropic hγ hx))
    (indL γ.symm (fun y hy => stabilizer_symm_maps_orthogonal hγ hy) (fun x hx => stabilizer_symm_maps_isotropic hγ hx))
    (by
      refine LinearMap.ext fun q => ?_
      induction q using Submodule.Quotient.induction_on with | H a => ?_
      rw [LinearMap.comp_apply, indL_mk, indL_mk, LinearMap.id_apply]
      congr 1
      apply Subtype.ext
      simp)
    (by
      refine LinearMap.ext fun q => ?_
      induction q using Submodule.Quotient.induction_on with | H a => ?_
      rw [LinearMap.comp_apply, indL_mk, indL_mk, LinearMap.id_apply]
      congr 1
      apply Subtype.ext
      simp)

theorem indE_mk {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) (a : perpS (VS D) F0.X) :
    indE hγ (Submodule.Quotient.mk a) = Submodule.Quotient.mk ⟨γ a, stabilizer_maps_orthogonal hγ a.2⟩ := rfl

theorem autLz_sub (Λ : Submodule (𝓞 D.host.E) (VS D).V) (φ : WbQ D F0 → WbQ D F0) (hφ : φ ∈ autLz D F0 Λ) :
    φ ∈ (fun σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0 => (σ : WbQ D F0 → WbQ D F0)) ''
      stabZ (hWb D F0) (zbar D F0) (Mof D F0 Λ) := by
  obtain ⟨γ, hγ, hγΛ, hφ⟩ := hφ
  refine ⟨indE hγ, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro x y
    induction x using Submodule.Quotient.induction_on with | H a => ?_
    induction y using Submodule.Quotient.induction_on with | H b => ?_
    rw [indE_mk, indE_mk, hWb_mk, hWb_mk]
    exact hγ.1 _ _
  · rw [zbar, indE_mk]
    congr 1
    apply Subtype.ext
    exact hγ.2.2
  · apply le_antisymm
    · rintro _ ⟨m, hm, rfl⟩
      obtain ⟨b, hbΛ, rfl⟩ := (mem_Mof D F0 Λ m).1 hm
      show indE hγ (Submodule.Quotient.mk b) ∈ Mof D F0 Λ
      rw [indE_mk, mem_Mof]
      refine ⟨_, ?_, rfl⟩
      rw [← hγΛ]
      exact Submodule.mem_map_of_mem hbΛ
    · intro m hm
      obtain ⟨b, hbΛ, rfl⟩ := (mem_Mof D F0 Λ m).1 hm
      have hb' : γ.symm b ∈ Λ := by
        rw [← hγΛ] at hbΛ
        obtain ⟨l, hl, hlb⟩ := hbΛ
        rw [← hlb]
        simpa using hl
      refine ⟨Submodule.Quotient.mk ⟨γ.symm b, stabilizer_symm_maps_orthogonal hγ b.2⟩, (mem_Mof D F0 Λ _).2 ⟨_, hb', rfl⟩, ?_⟩
      show indE hγ (Submodule.Quotient.mk ⟨γ.symm b, stabilizer_symm_maps_orthogonal hγ b.2⟩) = Submodule.Quotient.mk b
      rw [indE_mk]
      congr 1
      apply Subtype.ext
      simp
  · funext q
    induction q using Submodule.Quotient.induction_on with | H a => ?_
    show indE hγ (Submodule.Quotient.mk a) = φ (Submodule.Quotient.mk a)
    rw [indE_mk, hφ a]

theorem autLz_eq (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hL : Submodule.IsLattice D.host.E Λ)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) :
    autLz D F0 Λ = (fun σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0 => (σ : WbQ D F0 → WbQ D F0)) ''
      stabZ (hWb D F0) (zbar D F0) (Mof D F0 Λ) := by
  ext φ
  constructor
  · exact autLz_sub Λ φ
  · rintro ⟨σ, hσ, rfl⟩
    exact lift Λ hL hU σ hσ

end Induced

theorem row_weight_formula : RowWeight := by
  intro D u F0 Λ hrow
  obtain ⟨_, ⟨hL, hU, _, _⟩, _⟩ := hrow
  rw [autLz_eq Λ hL hU]
  exact Nat.card_image_of_injective DFunLike.coe_injective _

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowWeightPf

theorem PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.row_weight_formula : PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowWeight :=
  PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowWeightPf.row_weight_formula
end
end
end
