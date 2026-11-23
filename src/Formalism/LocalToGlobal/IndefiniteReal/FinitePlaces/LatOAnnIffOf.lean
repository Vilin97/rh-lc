module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PairingRankOneMemInverseDifferent
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharLem
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharStd
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatMod
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharStd
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatAnn

-- Source module: Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FiniteIdempotentMulEq

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct



namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Datum

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

def incInf (D : D7) : Ainf D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  TensorProduct.map (LinearMap.inl D.host.F (Ainf D.host.F) (Af D.host.F)) LinearMap.id

theorem inf_mul (z : AE D) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0) * z = incInf D (infPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [mul_zero, map_zero, map_zero]
  | tmul a e =>
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    show _ = incInf D (fstA D.host.F a ⊗ₜ[D.host.F] e)
    have : pairA D.host.F 1 0 * a = (fstA D.host.F a, (0 : Af D.host.F)) :=
      Prod.ext (by show (1 : Ainf D.host.F) * a.1 = a.1; rw [one_mul]) (by show (0 : Af D.host.F) * a.2 = 0; rw [zero_mul])
    rw [this]; rfl
  | add x y hx hy => rw [mul_add, hx, hy, map_add (f := _), map_add (f := _)]

theorem finite_idempotent_mul_eq (z : AE D) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 1) * z = jF D (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [mul_zero, map_zero, map_zero]
  | tmul a e =>
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, finPart_tmul, jF_tmul]
    congr 1
    exact Prod.ext (by show (0 : Ainf D.host.F) * a.1 = 0; rw [zero_mul]) (by show (1 : Af D.host.F) * a.2 = a.2; rw [one_mul])
  | add x y hx hy => rw [mul_add, hx, hy, map_add (f := _), map_add (f := _)]

theorem eq_jF_of_inf (z : AE D) (hz : infPart D z = 0) : z = jF D (finPart D z) := by
  have h1 : pairA D.host.F 1 0 + pairA D.host.F 0 1 = (1 : AF D.host.F) := Prod.ext (add_zero _) (zero_add _)
  calc z = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0 + pairA D.host.F 0 1) * z := by rw [h1, map_one, one_mul]
    _ = jF D (finPart D z) := by rw [map_add (f := _), add_mul, inf_mul, hz, map_zero, zero_add, finite_idempotent_mul_eq]

theorem finPart_jF (y : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (jF D y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a e => rw [jF_tmul, finPart_tmul]; rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem infPart_jF (y : Af D.host.F ⊗[D.host.F] D.host.E) : infPart D (jF D y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a e =>
    rw [jF_tmul]
    show (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)) (pairA D.host.F 0 a ⊗ₜ[D.host.F] e) = 0
    rw [Algebra.TensorProduct.map_tmul]
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] _ = 0
    rw [TensorProduct.zero_tmul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]

theorem approx_Af (a : Af D.host.F) (N : ℕ) (hN : 0 < N) :
    ∃ f : D.host.F, ∃ c ∈ intAf D.host.F, a = algebraMap D.host.F (Af D.host.F) f + algebraMap D.host.F (Af D.host.F) N * c := by
  have hNF : (N : D.host.F) ≠ 0 := by exact_mod_cast hN.ne'
  obtain ⟨u, hu⟩ := ReciprocityTheory.UG.AdeleIntA.exists_approx_adele (R := 𝓞 D.host.F)
    (algebraMap D.host.F (Af D.host.F) (1 / (N : D.host.F)) * a)
  refine ⟨N * u, _, intAf_of_isInt _ hu, ?_⟩
  rw [mul_sub, ← mul_assoc, ← map_mul, mul_one_div_cancel hNF, map_one, one_mul, ← map_mul]
  ring

theorem isAlg_Z (e : D.host.E) : IsAlgebraic ℤ e :=
  (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic e)



theorem approx_AfE (N : ℕ) (hN : 0 < N) (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    ∃ w : D.host.E, ∃ y ∈ intAE D, z = (1 : Af D.host.F) ⊗ₜ[D.host.F] w + N • y := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, by rw [TensorProduct.tmul_zero, smul_zero, add_zero]⟩
  | tmul a e =>
    obtain ⟨m, hm0, hmint⟩ := IsAlgebraic.exists_integral_multiple (isAlg_Z e)
    have hmF : ((m : ℤ) : D.host.F) ≠ 0 := by exact_mod_cast hm0
    let e' : 𝓞 D.host.E := ⟨m • e, hmint⟩
    have he : e = (1 / (m : D.host.F)) • (e' : D.host.E) := by
      show e = (1 / (m : D.host.F)) • (m • e)
      rw [zsmul_eq_mul, Algebra.smul_def, ← mul_assoc, ← map_intCast (algebraMap D.host.F D.host.E), ← map_mul,
        one_div_mul_cancel hmF, map_one, one_mul]
    obtain ⟨f, c, hc, hfc⟩ := approx_Af ((1 / (m : D.host.F)) • a) N hN
    refine ⟨f • (e' : D.host.E), c ⊗ₜ[D.host.F] (e' : D.host.E), AddSubgroup.subset_closure ⟨c, hc, e', rfl⟩, ?_⟩
    have hN' : algebraMap D.host.F (Af D.host.F) (N : D.host.F) * c = N • c := by
      rw [map_natCast, nsmul_eq_mul]
    rw [he, ← TensorProduct.smul_tmul, hfc, TensorProduct.add_tmul, hN', Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul, TensorProduct.smul_tmul']
  | add x y hx hy =>
    obtain ⟨w, y1, hy1, rfl⟩ := hx
    obtain ⟨w', y2, hy2, rfl⟩ := hy
    exact ⟨w + w', y1 + y2, add_mem hy1 hy2, by rw [TensorProduct.tmul_add, smul_add]; abel⟩

end Formalism.IndefR.Fin

end
end
end

-- Source module: Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatOAnnIffOf

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct



namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Datum

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}



theorem exists_sub_pairA_ratW_mem_latO (S T : HSp D) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hbox : ∃ N : ℕ, 0 < N ∧ ∀ Y : WO S T, (∀ i j, finPart D (Y i j) ∈ intAE D) → (∀ i j, infPart D (Y i j) = 0) →
      N • Y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True))
    (x : WO S T) (hx : x.map (infPart D) = 0) :
    ∃ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, x - pairA D.host.F 0 1 • ratW T S γ ∈
      latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  obtain ⟨N, hN, hbox⟩ := hbox
  have hdec : ∀ i j, ∃ w : D.host.E, ∃ y ∈ intAE D, finPart D (x i j) = (1 : Af D.host.F) ⊗ₜ[D.host.F] w + N • y :=
    fun i j => approx_AfE N hN (finPart D (x i j))
  choose w y hy hwy using hdec
  refine ⟨Matrix.of w, ?_⟩
  have hY : x - pairA D.host.F 0 1 • ratW T S (Matrix.of w) = N • (Matrix.of fun i j => jF D (y i j) : WO S T) := by
    ext i j
    have hxij : infPart D (x i j) = 0 := by
      have := congrFun (congrFun hx i) j
      simpa using this
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.of_apply, eq_jF_of_inf (x i j) hxij, hwy,
      map_add, map_nsmul]
    have h1 : jF D ((1 : Af D.host.F) ⊗ₜ[D.host.F] w i j) = pairA D.host.F 0 1 • ratW T S (Matrix.of w) i j := by
      rw [jF_tmul, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      show _ = (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] w i j)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h1, add_sub_cancel_left]
  rw [hY]
  apply hbox
  · intro i j; rw [Matrix.of_apply, finPart_jF]; exact hy i j
  · intro i j; rw [Matrix.of_apply, infPart_jF]



theorem ann_rat_mem (hψ : IsStdChar D ψ (-1)) (S T : HSp D) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hglob : ∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
      (∀ c ∈ D.host.AA, ∀ s ∈ ΛS, ∀ t ∈ ΛT, betaO S T γ (rk1 S T c s t) ∈ invDiff D.host.F) →
      γ ∈ Submodule.span ℤ {M | ∃ c ∈ D.host.AA, ∃ s ∈ ΛS, ∃ t ∈ ΛT, M = rk1 S T c s t})
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E)
    (hann : ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      ψ (symplO S T (pairA D.host.F 0 1 • ratW T S γ) u) = 1) :
    pairA D.host.F 0 1 • ratW T S γ ∈
      latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  have hb : ∀ c ∈ D.host.AA, ∀ s ∈ ΛS, ∀ t ∈ ΛT, betaO S T γ (rk1 S T c s t) ∈ invDiff D.host.F := by
    intro c hc s hs t ht y
    have hmem := gen_mem S T ΛS ΛT (intAf_int y) hc hs ht
    rw [gen_eq] at hmem
    have h := hann _ hmem
    rw [symplO_smul_left, symplO_smul_right, symplO_ratW_ratW] at h
    have e : pairA D.host.F 0 1 * (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (y : D.host.F)) *
        algebraMap D.host.F (AF D.host.F) (betaO S T γ (rk1 S T c s t))) =
        pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (betaO S T γ (rk1 S T c s t) * (y : D.host.F))) := by
      refine Prod.ext (by show (0 : Ainf D.host.F) * (0 * _) = 0; rw [zero_mul]) ?_
      change 1 * (algebraMap D.host.F (Af D.host.F) (y : D.host.F) *
        algebraMap D.host.F (Af D.host.F) (betaO S T γ (rk1 S T c s t))) =
        algebraMap D.host.F (Af D.host.F) (betaO S T γ (rk1 S T c s t) * (y : D.host.F))
      rw [map_mul]; ring
    rw [e, psi_fin_rat hψ] at h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
    refine ⟨n, ?_⟩
    have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : ((Algebra.trace ℚ D.host.F (betaO S T γ (rk1 S T c s t) * (y : D.host.F)) : ℚ) : ℂ) = (n : ℂ) := by
      have := hn
      rw [mul_comm (2 * (Real.pi : ℂ) * Complex.I)] at this
      exact mul_right_cancel₀ h2pi this
    exact_mod_cast this
  have hsp := hglob γ hb
  clear hb hann
  induction hsp using Submodule.span_induction with
  | mem M hM =>
    obtain ⟨c, hc, s, hs, t, ht, rfl⟩ := hM
    have := gen_mem S T ΛS ΛT one_intAf hc hs ht
    rwa [gen_eq] at this
  | zero =>
    rw [show ratW T S (0 : Matrix (Fin T.rank) (Fin S.rank) D.host.E) = 0 by ext i j; simp [ratW], smul_zero]
    exact zero_mem _
  | add M M' _ _ h1 h2 =>
    rw [show ratW T S (M + M') = ratW T S M + ratW T S M' by ext i j; simp [ratW], smul_add]
    exact add_mem h1 h2
  | smul n M _ h =>
    rw [show ratW T S (n • M) = n • ratW T S M by ext i j; simp [ratW, zsmul_eq_mul], smul_comm]
    exact zsmul_mem h n

theorem latO_ann_iff_of (hψ : IsStdChar D ψ (-1)) (S T : HSp D) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (hbox : ∃ N : ℕ, 0 < N ∧ ∀ Y : WO S T, (∀ i j, finPart D (Y i j) ∈ intAE D) → (∀ i j, infPart D (Y i j) = 0) →
      N • Y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True))
    (hglob : ∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
      (∀ c ∈ D.host.AA, ∀ s ∈ ΛS, ∀ t ∈ ΛT, betaO S T γ (rk1 S T c s t) ∈ invDiff D.host.F) →
      γ ∈ Submodule.span ℤ {M | ∃ c ∈ D.host.AA, ∃ s ∈ ΛS, ∃ t ∈ ΛT, M = rk1 S T c s t})
    (x : WO S T) (hx : x.map (infPart D) = 0) :
    x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
      ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        ψ (symplO S T x u) = 1 := by
  constructor
  · intro hxm u hu; exact lat_ann hψ S T hS hT hxm hu
  · intro hann
    obtain ⟨γ, hγ⟩ := exists_sub_pairA_ratW_mem_latO S T hbox x hx
    have hann' : ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        ψ (symplO S T (pairA D.host.F 0 1 • ratW T S γ) u) = 1 := by
      intro u hu
      have h1 := hann u hu
      have h2 := lat_ann hψ S T hS hT hγ hu
      have e : pairA D.host.F 0 1 • ratW T S γ = x - (x - pairA D.host.F 0 1 • ratW T S γ) := by abel
      rw [e, show x - (x - pairA D.host.F 0 1 • ratW T S γ) = x + -(x - pairA D.host.F 0 1 • ratW T S γ) by abel,
        symplO_add_left, symplO_neg_left, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, h1, h2, inv_one, one_mul]
    have hr := ann_rat_mem hψ S T hglob γ hann'
    have : x = (x - pairA D.host.F 0 1 • ratW T S γ) + pairA D.host.F 0 1 • ratW T S γ := by abel
    rw [this]; exact add_mem hγ hr

end Formalism.IndefR.Fin

end
end
end
