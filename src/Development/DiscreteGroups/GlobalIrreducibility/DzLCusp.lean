module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrincipalCongruenceFixedVectorsLeSmoothVectors
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.DiscreteGroups.GlobalIrreducibility.DzLcFin
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
public import GroundTheory.AutomorphicForms.GLnLocal
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.LocalField
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.AutomorphicForms.LocallyProfinite
public import Development.DiscreteGroups.GlobalIrreducibility.DzLcPerm
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff

-- Source module: Development.DiscreteGroups.GlobalIrreducibility.DzLcIso

section

@[expose] public section

noncomputable section

open GroundTheory.Automorphic

namespace DiscreteGroups.sglob.DzLc

variable {g : ℕ} [Fact g.Prime] {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

theorem norm_symm_le_one (i : ℚ_[g] ≃+* k) (hi : Continuous i) {x : k}
    (hx : x ∈ (ValuativeRel.valuation k).integer) : ‖i.symm x‖ ≤ 1 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨y, hy⟩ : ∃ y, i.symm x = y := ⟨_, rfl⟩
  rw [hy] at hlt
  have hix : i y = x := by rw [← hy, RingEquiv.apply_symm_apply]
  have hy0 : y ≠ 0 := fun h => by rw [h, norm_zero] at hlt; exact absurd hlt (by norm_num)
  have hx0 : x ≠ 0 := by rw [← hix]; exact (map_ne_zero i).2 hy0
  have hz : ‖y⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hlt
  have hϖ1 : ValuativeRel.valuation k (GLnLocal.uniformizer k : k) < 1 := GLnLocal.valuation_uniformizer_lt_one k
  have hϖ0 : (GLnLocal.uniformizer k : k) ≠ 0 := fun h =>
    GLnLocal.valuation_uniformizer_ne_zero k (by rw [h, map_zero])
  have h1 : Filter.Tendsto (fun m : ℕ => y⁻¹ ^ m * i.symm (GLnLocal.uniformizer k : k)⁻¹) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz).mul_const (i.symm (GLnLocal.uniformizer k : k)⁻¹)
  have hT : Filter.Tendsto (fun m : ℕ => i (y⁻¹ ^ m * i.symm (GLnLocal.uniformizer k : k)⁻¹)) Filter.atTop
      (nhds 0) := by
    have := (hi.tendsto 0).comp h1
    rwa [map_zero] at this
  have hO : ((ValuativeRel.valuation k).integer : Set k) ∈ nhds (0 : k) :=
    Valuation.isOpen_integer.mem_nhds (zero_mem _)
  obtain ⟨m, hm⟩ := (hT.eventually hO).exists
  have hm' : i (y⁻¹ ^ m * i.symm (GLnLocal.uniformizer k : k)⁻¹) ∈ (ValuativeRel.valuation k).integer := hm
  have hval := (Valuation.mem_integer_iff _ _).1 hm'
  have hxv := (Valuation.mem_integer_iff _ _).1 hx
  have hiy : i (y⁻¹ ^ m * i.symm (GLnLocal.uniformizer k : k)⁻¹) * x ^ m = (GLnLocal.uniformizer k : k)⁻¹ := by
    rw [map_mul, map_pow, map_inv₀, hix, RingEquiv.apply_symm_apply, inv_pow,
      mul_comm ((x ^ m)⁻¹) _, mul_assoc, inv_mul_cancel₀ (pow_ne_zero m hx0), mul_one]
  have hle : ValuativeRel.valuation k (GLnLocal.uniformizer k : k)⁻¹ ≤ 1 := by
    rw [← hiy, map_mul, map_pow]
    exact mul_le_one' hval (pow_le_one' hxv m)
  have hge : (1 : ValuativeRel.ValueGroupWithZero k) ≤ ValuativeRel.valuation k (GLnLocal.uniformizer k : k) := by
    calc (1 : ValuativeRel.ValueGroupWithZero k)
        = ValuativeRel.valuation k ((GLnLocal.uniformizer k : k) * (GLnLocal.uniformizer k : k)⁻¹) := by
          rw [mul_inv_cancel₀ hϖ0, map_one]
      _ = ValuativeRel.valuation k (GLnLocal.uniformizer k : k) *
          ValuativeRel.valuation k (GLnLocal.uniformizer k : k)⁻¹ := map_mul _ _ _
      _ ≤ ValuativeRel.valuation k (GLnLocal.uniformizer k : k) * 1 := by gcongr
      _ = _ := mul_one _
  exact absurd hϖ1 (not_lt.2 hge)

theorem exists_inc_eq (i : ℚ_[g] ≃+* k) (hi : Continuous i) {n : ℕ} (k0 : GL (Fin n) k)
    (hk : k0 ∈ GLnLocal.integralGL k n) :
    ∃ κ : GL (Fin n) ℤ_[g], Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n κ) = k0 := by
  obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff k n).1 hk
  let M : Matrix (Fin n) (Fin n) ℤ_[g] := fun a b =>
    ⟨i.symm ((k0 : Matrix (Fin n) (Fin n) k) a b), norm_symm_le_one i hi (h1 a b)⟩
  let M' : Matrix (Fin n) (Fin n) ℤ_[g] := fun a b =>
    ⟨i.symm (((k0⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) a b), norm_symm_le_one i hi (h2 a b)⟩
  let φ : ℤ_[g] →+* k := i.toRingHom.comp (algebraMap ℤ_[g] ℚ_[g])
  have hφ : Function.Injective φ := fun a b h => Subtype.ext (i.injective h)
  have hMφ : M.map φ = (k0 : Matrix (Fin n) (Fin n) k) := by
    ext a b
    exact i.apply_symm_apply _
  have hM'φ : M'.map φ = ((k0⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    ext a b
    exact i.apply_symm_apply _
  have hMM : M * M' = 1 := by
    apply Matrix.map_injective hφ
    show (M * M').map φ = (1 : Matrix (Fin n) (Fin n) ℤ_[g]).map φ
    rw [Matrix.map_mul, hMφ, hM'φ, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hM'M : M' * M = 1 := by
    apply Matrix.map_injective hφ
    show (M' * M).map φ = (1 : Matrix (Fin n) (Fin n) ℤ_[g]).map φ
    rw [Matrix.map_mul, hMφ, hM'φ, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero φ) (map_one φ)]
  refine ⟨⟨M, M', hMM, hM'M⟩, Matrix.GeneralLinearGroup.ext fun a b => ?_⟩
  exact i.apply_symm_apply _

theorem exists_lift (i : ℚ_[g] ≃+* k) {n a : ℕ} (u : GL (Fin n) (ZMod g))
    (hu : u ∈ GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a)) :
    ∃ κ : GL (Fin n) ℤ_[g], GlobalTheory.GLp.red g n κ = u ∧
      Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n κ) ∈
        GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a) := by
  classical
  have hu' := GlobalTheory.FiniteGL.mem_unipRadical.1 hu
  have hoff : ∀ x y, x ≠ y → GlobalTheory.FiniteGL.twoBlocks n a y ≤ GlobalTheory.FiniteGL.twoBlocks n a x →
      (u : Matrix (Fin n) (Fin n) (ZMod g)) x y = 0 := by
    intro x y hxy h
    have := hu' x y h
    rwa [Matrix.sub_apply, Matrix.one_apply_ne hxy, sub_zero] at this
  have hdiag : ∀ x, (u : Matrix (Fin n) (Fin n) (ZMod g)) x x = 1 := by
    intro x
    have := hu' x x le_rfl
    rwa [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at this
  let M : Matrix (Fin n) (Fin n) ℤ_[g] := fun x y =>
    if x = y then 1 else (((u : Matrix (Fin n) (Fin n) (ZMod g)) x y).val : ℤ_[g])
  have hM : (PadicInt.toZMod (p := g)).mapMatrix M = (u : Matrix (Fin n) (Fin n) (ZMod g)) := by
    ext x y
    show PadicInt.toZMod (M x y) = _
    simp only [M]
    split_ifs with h
    · subst h
      rw [map_one, hdiag]
    · rw [map_natCast, ZMod.natCast_zmod_val]
  have hd : IsUnit M.det := by
    by_contra h
    have h1 : M.det ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [PadicInt.ker_toZMod]
      exact h
    rw [RingHom.mem_ker, RingHom.map_det, hM] at h1
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit u)).ne_zero h1
  refine ⟨((Matrix.isUnit_iff_isUnit_det _).2 hd).unit, Units.ext hM, ?_⟩
  refine GlobalTheory.FiniteGL.mem_unipRadical.2 fun x y hxy => ?_
  rw [Matrix.sub_apply]
  show i.toRingHom (algebraMap ℤ_[g] ℚ_[g] (M x y)) - (1 : Matrix (Fin n) (Fin n) k) x y = 0
  by_cases h : x = y
  · subst h
    simp [M]
  · have h0 := hoff x y h hxy
    simp [M, h, h0]

end DiscreteGroups.sglob.DzLc
end
end
end

-- Source module: Development.DiscreteGroups.GlobalIrreducibility.DzLCusp

section

@[expose] public section

noncomputable section

open GlobalTheory.GLq GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LocGL GlobalTheory.LocLanglands
open scoped Classical

namespace DiscreteGroups.sglob.DzLc

variable {g : ℕ} [Fact g.Prime] {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

theorem twKer_twoBlocks_eq_top (i : ℚ_[g] ≃+* k) (hi : Continuous i) {n a : ℕ} (h0 : 0 < a) (ha : a < n)
    (τ : FDRep ℂ (Gn g n)) (hτ : GlobalTheory.GLq.IsCusp τ.character) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) k))
    (hs : GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ) :
    twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 = ⊤ := by
  obtain ⟨φ, hφ0, hφ⟩ := hs
  have hgen : ∀ x : GL (Fin n) k, x ∈ GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a) → ∀ v,
      σ.ρ x v - v ∈ twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 := by
    intro x hx v
    refine Submodule.subset_span ⟨⟨x, hx⟩, v, ?_⟩
    simp
  have hφT : ∀ w, φ w ∈ twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 := by
    intro w
    have hfin := sum_unip_eq_zero τ hτ h0 ha
    have key : ∀ u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a),
        φ w - φ (τ.ρ (u : Gn g n) w) ∈ twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 := by
      intro u
      obtain ⟨κ, hred, hmem⟩ := exists_lift i (u : Gn g n) u.2
      have h1 := hφ κ w
      rw [hred] at h1
      rw [h1, ← neg_sub]
      exact Submodule.neg_mem _ (hgen _ hmem (φ w))
    have hsum : ∑ u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a),
        (φ w - φ (τ.ρ (u : Gn g n) w)) =
          (Fintype.card (GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a)) : ℂ) • φ w := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_sub_distrib, ← map_sum φ (fun u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a) => τ.ρ (u : Gn g n) w),
        ← LinearMap.sum_apply Finset.univ
          (fun u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a) => τ.ρ (u : Gn g n)) w, hfin, LinearMap.zero_apply, map_zero,
        sub_zero, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    have hc : (Fintype.card (GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a)) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have hmem := Submodule.sum_mem _ fun u (_ : u ∈ Finset.univ) => key u
    rw [hsum] at hmem
    have := Submodule.smul_mem _
      (Fintype.card (GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a)) : ℂ)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  have hall : ∀ (h : GL (Fin n) k) (w : τ),
      σ.ρ h (φ w) ∈ twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 := by
    intro h w
    obtain ⟨p, hp, k0, hk0, rfl⟩ :=
      GroundTheory.Automorphic.Iwasawa.exists_blockUpper_mul_integralGL k n (monotone_twoBlocks (N := n) a) h
    obtain ⟨κ, rfl⟩ := exists_inc_eq i hi k0 hk0
    rw [map_mul, Module.End.mul_apply]
    refine twKer_le_comap σ.ρ _ p (blockUpper_le_normalizer (GlobalTheory.FiniteGL.twoBlocks n a) hp) ?_
    have h1 := hφ κ w
    rw [show (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) (GlobalTheory.GLp.inc g n κ) (φ w) =
      σ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n κ)) (φ w) from rfl] at h1
    rw [← h1]
    exact hφT _
  obtain ⟨w0, hw0⟩ : ∃ w, φ w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hφ0 (LinearMap.ext hcon)
  let S : Subrepresentation σ.ρ :=
    ⟨Submodule.span ℂ {v | ∃ (h : GL (Fin n) k) (w : τ), v = σ.ρ h (φ w)}, fun x v hv => by
      refine (Submodule.span_le.2 ?_ : _ ≤ (Submodule.span ℂ _).comap (σ.ρ x)) hv
      rintro _ ⟨h, w, rfl⟩
      exact Submodule.subset_span ⟨x * h, w, by rw [map_mul, Module.End.mul_apply]⟩⟩
  have hST : S.toSubmodule ≤ twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 :=
    Submodule.span_le.2 (by rintro _ ⟨h, w, rfl⟩; exact hall h w)
  have hirr := σ.irr
  rcases eq_bot_or_eq_top S with hS | hS
  · exfalso
    have hm : φ w0 ∈ S.toSubmodule := Submodule.subset_span ⟨1, w0, by rw [map_one, Module.End.one_apply]⟩
    rw [hS] at hm
    exact hw0 ((Submodule.mem_bot ℂ).1 hm)
  · refine eq_top_iff.2 fun v _ => hST ?_
    rw [hS]
    trivial

theorem isCuspidal_of_inflates (i : ℚ_[g] ≃+* k) (hi : Continuous i) {n : ℕ} (τ : FDRep ℂ (Gn g n))
    (hτ : GlobalTheory.GLq.IsCusp τ.character) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) k))
    (hs : GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ) :
    IsCuspidal σ.ρ := by
  refine ⟨σ.smooth, fun s d e he => ?_⟩
  obtain ⟨Q, a, h0, ha, hQ⟩ := exists_perm_conj e he
  have htop := twKer_twoBlocks_eq_top i hi h0 ha τ hτ σ hs
  have hinvQ : ∀ z, σ.ρ Q⁻¹ (σ.ρ Q z) = z := fun z => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hmap : twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 ≤
      (twKer σ.ρ (unipRad k e) 1).comap (σ.ρ Q) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨x, hx⟩, y, rfl⟩
    refine Submodule.subset_span ⟨⟨Q * x * Q⁻¹, hQ x hx⟩, σ.ρ Q y, ?_⟩
    simp [map_mul, Module.End.mul_apply, hinvQ]
  refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun v _ => ?_)
  have hv : σ.ρ Q⁻¹ v ∈ twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 := by
    rw [htop]
    exact Submodule.mem_top
  have := hmap hv
  rwa [Submodule.mem_comap, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] at this

end DiscreteGroups.sglob.DzLc

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end DiscreteGroups.sglob.DzType
end
end
end
