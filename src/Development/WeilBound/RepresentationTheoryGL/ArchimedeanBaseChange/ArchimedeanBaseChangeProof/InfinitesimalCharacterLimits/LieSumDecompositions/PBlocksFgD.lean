module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksFgA
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.SplitInv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceTensA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksFgC

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksFgB

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs GlobalTheory.SmGL

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration

set_option linter.unusedSectionVars false

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Curve

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

def ecurve {N : ℕ} (Z : Matrix (Fin N) (Fin N) (Cinf E)) (t : ℝ) : Matrix (Fin N) (Fin N) (Cinf E) :=
  NormedSpace.exp (t • Z)

theorem hasDerivAt_ecurve {N : ℕ} (Z : Matrix (Fin N) (Fin N) (Cinf E)) : HasDerivAt (ecurve Z) Z 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Z (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact h

theorem ecurve_zero {N : ℕ} (Z : Matrix (Fin N) (Fin N) (Cinf E)) : ecurve Z 0 = 1 := by
  simp [ecurve]

theorem ecurve_mem {N : ℕ} (Z : Matrix (Fin N) (Fin N) (Cinf E)) (hZ : Zᴴ = -Z) (t : ℝ) :
    ecurve Z t ∈ Matrix.unitaryGroup (Fin N) (Cinf E) := by
  have hc : (t • Z)ᴴ = -(t • Z) := by
    rw [conjTranspose_smul, hZ]; simp
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ecurve, ← Matrix.exp_conjTranspose, hc,
    ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Z)).neg_right]
  simp

def toLclm (N : ℕ) : Matrix (Fin N) (Fin N) (Cinf E) →L[ℝ] Lie E N :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => toL A, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

theorem hasDerivAt_toL_ecurve {N : ℕ} (Z : Matrix (Fin N) (Fin N) (Cinf E)) :
    HasDerivAt (fun t => (toL (ecurve Z t) : Lie E N)) (toL Z) 0 := by
  have h := ((toLclm (E := E) N).hasFDerivAt (x := ecurve Z 0)).comp_hasDerivAt (0 : ℝ) (hasDerivAt_ecurve Z)
  exact h

end Curve

def kcurve {N : ℕ} (Z : Matrix (Fin N) (Fin N) (Cinf E)) (hZ : Zᴴ = -Z) (t : ℝ) : Kinf E N :=
  ⟨ecurve Z t, ecurve_mem Z hZ t⟩

theorem lie_mem_orbSpan {N : ℕ} (φ : Sm E N) [FiniteDimensional ℂ (GlobalTheory.CuspRep.LocEx.orbSpan φ)]
    (Z : Matrix (Fin N) (Fin N) (Cinf E)) (hZ : Zᴴ = -Z) :
    lie E N (toL Z) φ ∈ GlobalTheory.CuspRep.LocEx.orbSpan φ := by
  set A : Submodule ℂ (GA E N → ℂ) := (GlobalTheory.CuspRep.LocEx.orbSpan φ).map (Sm E N).subtype with hA
  have : FiniteDimensional ℂ A := inferInstance
  obtain ⟨S, a, ha⟩ := SliceTensor.interp A
  let c : ℝ → GL (Fin N) (Cinf E) := fun t => Unitary.toUnits (kcurve Z hZ t)
  have h0 : c 0 = 1 := Units.ext (ecurve_zero Z)
  have hc : HasDerivAt (fun t => toL (c t).val) (toL Z) 0 := hasDerivAt_toL_ecurve Z
  have hmem : ∀ t, (cptRep E N (kcurve Z hZ t) φ).1 ∈ A := fun t =>
    ⟨_, Submodule.subset_span ⟨kcurve Z hZ t, rfl⟩, rfl⟩
  have hval : ∀ t g, (cptRep E N (kcurve Z hZ t) φ).1 g = φ.1 (g * infGL E N (c t)) := fun _ _ => rfl
  have key : ∀ g, lieD (toL Z) φ.1 g = ∑ κ : S, lieD (toL Z) φ.1 κ.1 * (a κ : GA E N → ℂ) g := by
    intro g
    have e : ∀ t, φ.1 (g * infGL E N (c t)) = ∑ κ : S, φ.1 (κ.1 * infGL E N (c t)) * (a κ : GA E N → ℂ) g := by
      intro t
      have := congrFun (ha _ (hmem t)) g
      rw [hval, Finset.sum_apply] at this
      rw [this]
      refine Finset.sum_congr rfl fun κ _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, hval]
    have d1 := hasDerivAt_curve φ g c (toL Z) h0 hc
    have d2 : HasDerivAt (fun t => ∑ κ : S, φ.1 (κ.1 * infGL E N (c t)) * (a κ : GA E N → ℂ) g)
        (∑ κ : S, lieD (toL Z) φ.1 κ.1 * (a κ : GA E N → ℂ) g) 0 :=
      HasDerivAt.fun_sum fun κ _ => (hasDerivAt_curve φ κ.1 c (toL Z) h0 hc).mul_const _
    rw [show (fun t => φ.1 (g * infGL E N (c t))) = fun t =>
      ∑ κ : S, φ.1 (κ.1 * infGL E N (c t)) * (a κ : GA E N → ℂ) g from funext e] at d1
    exact d1.unique d2
  have hL : (lie E N (toL Z) φ).1 ∈ A := by
    have e : (lie E N (toL Z) φ).1 = ∑ κ : S, lieD (toL Z) φ.1 κ.1 • (a κ : GA E N → ℂ) := by
      funext g
      rw [GlobalTheory.CuspRep.lie_apply, key g, Finset.sum_apply]
      rfl
    rw [e]
    exact A.sum_mem fun κ _ => A.smul_mem _ (a κ).2
  obtain ⟨y, hy, e⟩ := hL
  have : y = lie E N (toL Z) φ := Subtype.ext e
  rw [← this]
  exact hy

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksFgD

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs GlobalTheory.SmGL

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ}

def HExp (U : Submodule ℂ (Sm E (r + s))) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)) : Prop :=
  ∀ ψ ∈ U, ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)), ∃ (n : ℕ) (b : Fin n → Sm E r) (q : Fin n → Sm E s),
    (∀ i, b i ∈ Submodule.span ℂ (BlockDerivatives.lsF r s (T ψ) k g)) ∧ (∀ i, q i ∈ BlockDerivatives.rsF r s (T ψ) k g) ∧
    ∀ m : GA E r × GA E s, (T ψ).1 (lev (Ad E) r s m * BlockDerivatives.yp k g) = ∑ i, (b i).1 m.1 * (q i).1 m.2

theorem lsF_yp (F : Sm E (r + s)) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) :
    ∀ ℓ ∈ BlockDerivatives.lsF r s F k g, ∃ m₂, ℓ = sl0 m₂ (rt E (r + s) (BlockDerivatives.yp k g) F) := by
  rintro ℓ ⟨m₂, h⟩
  exact ⟨m₂, Subtype.ext (funext fun m₁ => by rw [h, left_slice_apply, rt_apply])⟩

theorem rsF_yp (F : Sm E (r + s)) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) :
    ∀ ℓ ∈ BlockDerivatives.rsF r s F k g, ∃ m₁, ℓ = sl1 m₁ (rt E (r + s) (BlockDerivatives.yp k g) F) := by
  rintro ℓ ⟨m₁, h⟩
  exact ⟨m₁, Subtype.ext (funext fun m₂ => by rw [h, right_slice_apply, rt_apply])⟩

theorem rt_one {a : ℕ} (F : Sm E a) : rt E a (BlockDerivatives.yp 1 1) F = F := by
  rw [yp_one, map_one, Module.End.one_apply]

theorem lsF_one (F : Sm E (r + s)) : ∀ ℓ ∈ BlockDerivatives.lsF r s F 1 1, ∃ m₂, ℓ = sl0 m₂ F := by
  intro ℓ hℓ
  obtain ⟨m₂, h⟩ := lsF_yp F 1 1 ℓ hℓ
  exact ⟨m₂, by rw [h, rt_one]⟩

theorem rsF_one (F : Sm E (r + s)) : ∀ ℓ ∈ BlockDerivatives.rsF r s F 1 1, ∃ m₁, ℓ = sl1 m₁ F := by
  intro ℓ hℓ
  obtain ⟨m₁, h⟩ := rsF_yp F 1 1 ℓ hℓ
  exact ⟨m₁, by rw [h, rt_one]⟩

theorem exp_one {U : Submodule ℂ (Sm E (r + s))} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)} (hexp : HExp U T)
    {ψ : Sm E (r + s)} (hψ : ψ ∈ U) :
    ∃ (n : ℕ) (b : Fin n → Sm E r) (q : Fin n → Sm E s),
      (∀ i, b i ∈ Submodule.span ℂ (BlockDerivatives.lsF r s (T ψ) 1 1)) ∧ (∀ i, q i ∈ BlockDerivatives.rsF r s (T ψ) 1 1) ∧
      ∀ m : GA E r × GA E s, (T ψ).1 (lev (Ad E) r s m) = ∑ i, (b i).1 m.1 * (q i).1 m.2 := by
  obtain ⟨n, b, q, hb, hq, he⟩ := hexp ψ hψ 1 1
  refine ⟨n, b, q, hb, hq, fun m => ?_⟩
  rw [← he m, yp_one, mul_one]

theorem rt_yp_eq {a : ℕ} (k : Kinf E a) (g : GL (Fin a) (Af E)) (φ : Sm E a) :
    rt E a (BlockDerivatives.yp k g) φ = act (.cpt k) (act (.fin g) φ) := by
  rw [act_cpt_eq, act_fin_eq, rt_yp_rt, mul_one, one_mul]

theorem rt_yp_mem {a : ℕ} {U : Submodule ℂ (Sm E a)} (hU : _root_.GlobalTheory.CuspRep.IsStable U) (k : Kinf E a) (g : GL (Fin a) (Af E))
    {φ : Sm E a} (hφ : φ ∈ U) : rt E a (BlockDerivatives.yp k g) φ ∈ U := by
  rw [rt_yp_eq]
  exact hU _ _ (hU _ _ hφ)

theorem T_rt_yp {a : ℕ} {U : Submodule ℂ (Sm E a)} (hU : _root_.GlobalTheory.CuspRep.IsStable U) {T : Sm E a →ₗ[ℂ] Sm E a}
    (hT : ∀ o, ∀ φ ∈ U, T (act o φ) = act o (T φ)) (k : Kinf E a) (g : GL (Fin a) (Af E)) {φ : Sm E a}
    (hφ : φ ∈ U) : T (rt E a (BlockDerivatives.yp k g) φ) = rt E a (BlockDerivatives.yp k g) (T φ) := by
  rw [rt_yp_eq, rt_yp_eq, hT _ _ (hU _ _ hφ), hT _ _ hφ]

def Mleft (U : Submodule ℂ (Sm E (r + s))) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)) (W : Submodule ℂ (Sm E r)) :
    Submodule ℂ (Sm E (r + s)) where
  carrier := {ψ | ψ ∈ U ∧ ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₂ : GA E s),
    sl0 m₂ (T (rt E (r + s) (BlockDerivatives.yp k g) ψ)) ∈ W}
  add_mem' := fun {a b} ha hb => ⟨U.add_mem ha.1 hb.1, fun k g m₂ => by
    rw [map_add (f := _), map_add (f := _), map_add (f := _)]; exact W.add_mem (ha.2 k g m₂) (hb.2 k g m₂)⟩
  zero_mem' := ⟨U.zero_mem, fun k g m₂ => by rw [map_zero, map_zero, map_zero]; exact W.zero_mem⟩
  smul_mem' := fun c a ha => ⟨U.smul_mem c ha.1, fun k g m₂ => by
    rw [map_smul, map_smul, map_smul]; exact W.smul_mem c (ha.2 k g m₂)⟩

def Mright (U : Submodule ℂ (Sm E (r + s))) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)) (W : Submodule ℂ (Sm E s)) :
    Submodule ℂ (Sm E (r + s)) where
  carrier := {ψ | ψ ∈ U ∧ ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₁ : GA E r),
    sl1 m₁ (T (rt E (r + s) (BlockDerivatives.yp k g) ψ)) ∈ W}
  add_mem' := fun {a b} ha hb => ⟨U.add_mem ha.1 hb.1, fun k g m₁ => by
    rw [map_add (f := _), map_add (f := _), map_add (f := _)]; exact W.add_mem (ha.2 k g m₁) (hb.2 k g m₁)⟩
  zero_mem' := ⟨U.zero_mem, fun k g m₁ => by rw [map_zero, map_zero, map_zero]; exact W.zero_mem⟩
  smul_mem' := fun c a ha => ⟨U.smul_mem c ha.1, fun k g m₁ => by
    rw [map_smul, map_smul, map_smul]; exact W.smul_mem c (ha.2 k g m₁)⟩

theorem Mleft_stable {U : Submodule ℂ (Sm E (r + s))} (hU : IsAutSt U) {c : ℂ}
    {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)} (hT : IsSliceMap U c T) (hexp : HExp U T) (W : Submodule ℂ (Sm E r))
    (hW : _root_.GlobalTheory.CuspRep.IsStable W) : _root_.GlobalTheory.CuspRep.IsStable (Mleft U T W) := by
  rintro o ψ ⟨hψU, hψ⟩
  cases o with
  | fin h =>
    refine ⟨hU.1 _ _ hψU, fun k g m₂ => ?_⟩
    rw [act_fin_eq, rt_yp_rt, mul_one]
    exact hψ k (g * h) m₂
  | cpt κ =>
    refine ⟨hU.1 _ _ hψU, fun k g m₂ => ?_⟩
    rw [act_cpt_eq, rt_yp_rt, mul_one]
    exact hψ (k * κ) g m₂
  | lie X =>
    refine ⟨hU.1 _ _ hψU, fun k g m₂ => ?_⟩
    obtain ⟨X', hX'⟩ := rt_lie_yp k g X
    have hψ'U : rt E (r + s) (BlockDerivatives.yp k g) ψ ∈ U := rt_yp_mem hU.1 k g hψU
    have e1 : rt E (r + s) (BlockDerivatives.yp k g) (act (.lie X) ψ) = lie E (r + s) X' (rt E (r + s) (BlockDerivatives.yp k g) ψ) :=
      LinearMap.congr_fun hX' ψ
    rw [e1]
    have e2 := hT.equiv (.lie X') _ hψ'U
    change T (lie E (r + s) X' _) = lie E (r + s) X' _ at e2
    rw [e2]
    set ψ' := rt E (r + s) (BlockDerivatives.yp k g) ψ with hψ'
    have hP : ∀ m₂, sl0 m₂ (T ψ') ∈ W := fun m₂ => hψ k g m₂
    obtain ⟨n, b, q, hb, -, he⟩ := exp_one hexp hψ'U
    have hsub : BlockDerivatives.lsF r s (T ψ') 1 1 ⊆ W := fun ℓ hℓ => by
      obtain ⟨m, rfl⟩ := lsF_one _ ℓ hℓ
      exact hP m
    have hbW : ∀ i, b i ∈ W := fun i => (Submodule.span_le.2 hsub) (hb i)
    rw [lie_split, map_add (f := _)]
    refine W.add_mem (key_left W hW (T ψ') (hT.unipInv ψ' hψ'U) hP b q hbW he _ (par_low X') m₂) ?_
    have e3 := hT.equiv (.lie (toL (skw X'))) _ hψ'U
    change T (lie E (r + s) (toL (skw X')) ψ') = lie E (r + s) (toL (skw X')) (T ψ') at e3
    rw [← e3]
    have : FiniteDimensional ℂ (GlobalTheory.CuspRep.LocEx.orbSpan ψ') := (hU.2 ψ' hψ'U).kfin
    have hmem := lie_mem_orbSpan ψ' (skw X') (skw_skew X')
    have hle : GlobalTheory.CuspRep.LocEx.orbSpan ψ' ≤ W.comap (sl0 m₂ ∘ₗ T) := Submodule.span_le.2 (by
      rintro _ ⟨κ, rfl⟩
      change sl0 m₂ (T (act (.cpt κ) ψ')) ∈ W
      rw [act_cpt_eq, hψ', rt_yp_rt, one_mul]
      exact hψ (κ * k) g m₂)
    exact hle hmem

theorem Mright_stable {U : Submodule ℂ (Sm E (r + s))} (hU : IsAutSt U) {c : ℂ}
    {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)} (hT : IsSliceMap U c T) (hexp : HExp U T) (W : Submodule ℂ (Sm E s))
    (hW : _root_.GlobalTheory.CuspRep.IsStable W) : _root_.GlobalTheory.CuspRep.IsStable (Mright U T W) := by
  rintro o ψ ⟨hψU, hψ⟩
  cases o with
  | fin h =>
    refine ⟨hU.1 _ _ hψU, fun k g m₁ => ?_⟩
    rw [act_fin_eq, rt_yp_rt, mul_one]
    exact hψ k (g * h) m₁
  | cpt κ =>
    refine ⟨hU.1 _ _ hψU, fun k g m₁ => ?_⟩
    rw [act_cpt_eq, rt_yp_rt, mul_one]
    exact hψ (k * κ) g m₁
  | lie X =>
    refine ⟨hU.1 _ _ hψU, fun k g m₁ => ?_⟩
    obtain ⟨X', hX'⟩ := rt_lie_yp k g X
    have hψ'U : rt E (r + s) (BlockDerivatives.yp k g) ψ ∈ U := rt_yp_mem hU.1 k g hψU
    have e1 : rt E (r + s) (BlockDerivatives.yp k g) (act (.lie X) ψ) = lie E (r + s) X' (rt E (r + s) (BlockDerivatives.yp k g) ψ) :=
      LinearMap.congr_fun hX' ψ
    rw [e1]
    have e2 := hT.equiv (.lie X') _ hψ'U
    change T (lie E (r + s) X' _) = lie E (r + s) X' _ at e2
    rw [e2]
    set ψ' := rt E (r + s) (BlockDerivatives.yp k g) ψ with hψ'
    have hP : ∀ m₁, sl1 m₁ (T ψ') ∈ W := fun m₁ => hψ k g m₁
    obtain ⟨n, b, q, -, hq, he⟩ := exp_one hexp hψ'U
    have hqW : ∀ i, q i ∈ W := fun i => by
      obtain ⟨m, hm⟩ := rsF_one _ _ (hq i)
      rw [hm]
      exact hP m
    rw [lie_split, map_add (f := _)]
    refine W.add_mem (key_right W hW (T ψ') (hT.unipInv ψ' hψ'U) hP b q hqW he _ (par_low X') m₁) ?_
    have e3 := hT.equiv (.lie (toL (skw X'))) _ hψ'U
    change T (lie E (r + s) (toL (skw X')) ψ') = lie E (r + s) (toL (skw X')) (T ψ') at e3
    rw [← e3]
    have : FiniteDimensional ℂ (GlobalTheory.CuspRep.LocEx.orbSpan ψ') := (hU.2 ψ' hψ'U).kfin
    have hmem := lie_mem_orbSpan ψ' (skw X') (skw_skew X')
    have hle : GlobalTheory.CuspRep.LocEx.orbSpan ψ' ≤ W.comap (sl1 m₁ ∘ₗ T) := Submodule.span_le.2 (by
      rintro _ ⟨κ, rfl⟩
      change sl1 m₁ (T (act (.cpt κ) ψ')) ∈ W
      rw [act_cpt_eq, hψ', rt_yp_rt, one_mul]
      exact hψ (κ * k) g m₁)
    exact hle hmem

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration
end
end
end
