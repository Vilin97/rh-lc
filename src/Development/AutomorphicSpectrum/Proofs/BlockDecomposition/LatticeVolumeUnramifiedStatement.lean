module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps
import Aesop.Main
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicIntegersCompact.IsCompactAdicCompletionIntegers
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SelfDualVol

section

@[expose] public section

open MeasureTheory

namespace GlobalTheory.CompanionTheory.GunrVol

theorem selfDualVol : PositivityTheory.SiegelWeilFormula.Gunr.SelfDualVol := by
  intro V _ _ _ _ _ μ χ hsd L hLo hLc hadd _ hann
  obtain ⟨hH, hinv⟩ := hsd
  haveI := hH
  have hLcl : IsClosed (L : Set V) := AddSubgroup.isClosed_of_isOpen L hLo
  have hLm : MeasurableSet (L : Set V) := hLo.measurableSet
  have hfin : μ (L : Set V) ≠ ⊤ := hLc.measure_lt_top.ne
  have hpos : μ (L : Set V) ≠ 0 := (hLo.measure_pos μ ⟨0, L.zero_mem⟩).ne'
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : V → ℂ, Φ = (L : Set V).indicator 1 := ⟨_, rfl⟩
  have hΦin : ∀ x ∈ L, Φ x = 1 := fun x hx => by
    rw [hΦ]; exact Set.indicator_of_mem (s := (L : Set V)) hx _
  have hΦout : ∀ x, x ∉ L → Φ x = 0 := fun x hx => by
    rw [hΦ]; exact Set.indicator_of_notMem (s := (L : Set V)) hx _
  have hΦc : Continuous Φ := by
    rw [hΦ]
    exact continuous_one.indicator (by
      intro a ha
      rw [(IsClopen.frontier_eq ⟨hLcl, hLo⟩)] at ha
      exact absurd ha (Set.notMem_empty a))
  have hΦs : HasCompactSupport Φ := by
    refine HasCompactSupport.intro hLc ?_
    intro x hx
    exact hΦout x hx
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = μ.real (L : Set V) := ⟨_, rfl⟩
  have hI : ∀ y, ∫ x, Φ x * χ x y ∂μ = (L : Set V).indicator (fun _ => (m : ℂ)) y := by
    intro y
    by_cases hy : y ∈ L
    · have h1 : (fun x => Φ x * χ x y) = Φ := by
        funext x
        by_cases hx : x ∈ L
        · rw [(hann y).2 hy x hx, mul_one]
        · rw [hΦout x hx, zero_mul]
      rw [h1, Set.indicator_of_mem (s := (L : Set V)) hy, hΦ, integral_indicator hLm]
      simp [hm]
    · rw [Set.indicator_of_notMem (s := (L : Set V)) hy]
      have h2 := (hann y).not.2 hy
      push_neg at h2
      obtain ⟨x0, hx0, hne⟩ := h2
      have h3 : ∫ x, Φ x * χ x y ∂μ = χ x0 y * ∫ x, Φ x * χ x y ∂μ := by
        calc ∫ x, Φ x * χ x y ∂μ = ∫ x, (fun x => Φ x * χ x y) (x0 + x) ∂μ :=
              (integral_add_left_eq_self _ x0).symm
          _ = ∫ x, χ x0 y * (Φ x * χ x y) ∂μ := by
              congr 1
              funext x
              have : Φ (x0 + x) = Φ x := by
                by_cases hx : x ∈ L
                · rw [hΦin _ (L.add_mem hx0 hx), hΦin _ hx]
                · rw [hΦout _ (fun h => hx ((L.add_mem_cancel_left hx0).1 h)), hΦout _ hx]
              simp only [this, hadd]
              ring
          _ = χ x0 y * ∫ x, Φ x * χ x y ∂μ := integral_const_mul _ _
      have h4 : (1 - χ x0 y) * ∫ x, Φ x * χ x y ∂μ = 0 := by
        rw [sub_mul, one_mul, ← h3, sub_self]
      exact (mul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 (Ne.symm hne))
  have hInt : Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ := by
    rw [funext hI]
    exact (integrable_indicator_iff hLm).2 (integrableOn_const hfin)
  have h0 := hinv Φ hΦc hΦs hInt 0
  have hout : (fun y => (∫ x, Φ x * χ x y ∂μ) * χ y 0) = (L : Set V).indicator (fun _ => (m : ℂ)) := by
    funext y
    rw [hI]
    by_cases hy : y ∈ L
    · rw [(hann 0).2 L.zero_mem y hy, mul_one]
    · rw [Set.indicator_of_notMem (s := (L : Set V)) hy, zero_mul]
  rw [hout, integral_indicator hLm, neg_zero, hΦin 0 L.zero_mem] at h0
  have h5 : (m : ℂ) * m = 1 := by
    have := h0
    simp only [setIntegral_const, ← hm, Complex.real_smul] at this
    exact this
  have h6 : m * m = 1 := by exact_mod_cast h5
  have hm0 : 0 ≤ m := by rw [hm]; exact measureReal_nonneg
  have h7 : m = 1 := by nlinarith
  rw [hm, measureReal_def, ENNReal.toReal_eq_one_iff] at h7
  exact h7

end GlobalTheory.CompanionTheory.GunrVol
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeVolumeUnramified

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.GunrVol

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter Topology
open scoped TensorProduct
open PositivityTheory.SiegelWeilFormula.Gunr

section Top

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem finFE : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E

attribute [local instance] finFE

theorem isModTopA (v : HeightOneSpectrum (𝓞 F)) : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩

attribute [local instance] isModTopA

theorem isTopRingA (v : HeightOneSpectrum (𝓞 F)) : IsTopologicalRing (Fv F v ⊗[F] E) :=
  IsModuleTopology.isTopologicalRing (Fv F v) _

attribute [local instance] isTopRingA

theorem fv_sc (v : HeightOneSpectrum (𝓞 F)) : SecondCountableTopology (Fv F v) := by
  have : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  have : TopologicalSpace.SeparableSpace (Fv F v) :=
    TopologicalSpace.SeparableSpace.of_denseRange _ (HeightOneSpectrum.denseRange_algebraMap F v)
  exact UniformSpace.secondCountable_of_separable (Fv F v)

variable {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))

theorem continuous_crd (k : Fin d) :
    Continuous fun y : Fv F v ⊗[F] E => (Algebra.TensorProduct.basis (Fv F v) bs).repr y k :=
  IsModuleTopology.continuous_of_linearMap ((Algebra.TensorProduct.basis (Fv F v) bs).coord k)

theorem eq_sum_crd (y : Fv F v ⊗[F] E) :
    y = ∑ i, (Algebra.TensorProduct.basis (Fv F v) bs).repr y i • ((1 : Fv F v) ⊗ₜ[F] bs i) := by
  have := (Algebra.TensorProduct.basis (Fv F v) bs).sum_repr y
  simp only [Algebra.TensorProduct.basis_apply] at this
  exact this.symm

include bs in
theorem scA : SecondCountableTopology (Fv F v ⊗[F] E) := by
  haveI := fv_sc v
  let e := (Algebra.TensorProduct.basis (Fv F v) bs).equivFun
  let h : (Fv F v ⊗[F] E) ≃ₜ (Fin d → Fv F v) :=
    { e.toEquiv with
      continuous_toFun := continuous_pi fun k => continuous_crd bs v k
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }
  exact h.secondCountableTopology

theorem isClopen_lat (n M : ℕ) : IsClopen (latV (M := M) (n := n) bs v) := by
  have hc : ∀ (x : Fin n) (i : Fin M) (k : Fin d),
      Continuous (fun Y : Fin n → Fin M → Fv F v ⊗[F] E =>
        (Algebra.TensorProduct.basis (Fv F v) bs).repr (Y x i) k) :=
    fun x i k => (continuous_crd bs v k).comp ((continuous_apply i).comp (continuous_apply x))
  have e : latV (M := M) (n := n) bs v = ⋂ x, ⋂ i, ⋂ k,
      (fun Y : Fin n → Fin M → Fv F v ⊗[F] E =>
        (Algebra.TensorProduct.basis (Fv F v) bs).repr (Y x i) k) ⁻¹'
        (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    ext Y
    simp [latV]
  have hcl : IsClosed (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    (PI.IntAdCpctOpenWork.isCompact_adicCompletionIntegers v).isClosed
  have hop : IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    Valued.isOpen_valuationSubring _
  rw [e]
  exact ⟨isClosed_iInter fun x => isClosed_iInter fun i => isClosed_iInter fun k =>
    hcl.preimage (hc x i k), isOpen_iInter_of_finite fun x =>
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k => hop.preimage (hc x i k)⟩

theorem isCompact_lat (n M : ℕ) : IsCompact (latV (M := M) (n := n) bs v) := by
  let L : (Fin n → Fin M → Fin d → Fv F v) → (Fin n → Fin M → Fv F v ⊗[F] E) :=
    fun c x i => ∑ k, c x i k • ((1 : Fv F v) ⊗ₜ[F] bs k)
  have hL : Continuous L := by
    refine continuous_pi fun x => continuous_pi fun i => continuous_finsetSum _ fun k _ => ?_
    exact continuous_smul.comp
      (((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply x))).prodMk
        continuous_const)
  let K : Set (Fin n → Fin M → Fin d → Fv F v) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.pi Set.univ fun _ =>
      (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    isCompact_univ_pi fun _ => PI.IntAdCpctOpenWork.isCompact_adicCompletionIntegers v
  refine (hK.image hL).of_isClosed_subset (isClopen_lat bs v n M).isClosed ?_
  intro Y hY
  refine ⟨fun x i k => (Algebra.TensorProduct.basis (Fv F v) bs).repr (Y x i) k, ?_, ?_⟩
  · simp only [K, Set.mem_pi, Set.mem_univ, true_implies]
    intro x i k
    exact hY x i k
  · funext x i
    exact (eq_sum_crd bs v (Y x i)).symm

theorem continuous_sig (σ : E →ₐ[F] E) :
    Continuous (sigR (Fv F v) σ : Fv F v ⊗[F] E → Fv F v ⊗[F] E) := by
  let f : (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fv F v ⊗[F] E) :=
    { toFun := sigR (Fv F v) σ
      map_add' := map_add _
      map_smul' := fun c x => sigR_smul (v := v) σ c x }
  exact IsModuleTopology.continuous_of_linearMap f

theorem continuous_BR (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (Y : Fin n → Fin M → Fv F v ⊗[F] E) :
    Continuous fun X : Fin n → Fin M → Fv F v ⊗[F] E => BR (Fv F v) σ J X Y := by
  have htr : Continuous (Algebra.trace (Fv F v) (Fv F v ⊗[F] E)) :=
    IsModuleTopology.continuous_of_linearMap _
  unfold BR hR hform
  refine continuous_finsetSum _ fun a _ => htr.comp ?_
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (((continuous_sig v σ).comp ((continuous_apply i).comp (continuous_apply a))).mul
    continuous_const).mul continuous_const

end Top

section Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M n d : ℕ} {J : Matrix (Fin M) (Fin M) E} {T : Matrix (Fin n) (Fin n) E}
  {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ψv : Fv F v → ℂ}
  {S : Subring (Fv F v ⊗[F] E)} {σS : S →+* S} {ϖ : Fv F v} {ε : ℤ}

theorem BR_add (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E)
    (X X' Y : Fin n → Fin M → Fv F v ⊗[F] E) :
    BR (Fv F v) σ J (X + X') Y = BR (Fv F v) σ J X Y + BR (Fv F v) σ J X' Y := by
  simp only [BR, hR, hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem mem_S_iff (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (x : Fv F v ⊗[F] E) :
    x ∈ S ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) bs).repr x k ∈ v.adicCompletionIntegers F := by
  have : x ∈ (S : Set (Fv F v ⊗[F] E)) ↔ x ∈ Rv bs v := by rw [hG.carrier]
  exact this

theorem mem_lat_iff (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (Y : Fin n → Fin M → Fv F v ⊗[F] E) :
    Y ∈ latV (M := M) (n := n) bs v ↔ ∀ a i, Y a i ∈ S := by
  simp only [mem_S_iff hG]
  rfl

theorem alg_mem (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) {b : Fv F v}
    (hb : b ∈ v.adicCompletionIntegers F) :
    algebraMap (Fv F v) (Fv F v ⊗[F] E) b ∈ S := by
  rw [mem_S_iff hG]
  intro k
  have h1 := (mem_S_iff hG 1).1 S.one_mem k
  rw [Algebra.algebraMap_eq_smul_one, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact mul_mem hb h1

theorem sig_mem (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) {x : Fv F v ⊗[F] E} (hx : x ∈ S) :
    sigR (Fv F v) σ x ∈ S := by
  have := hG.sig ⟨x, hx⟩
  simp only at this
  rw [← this]
  exact (σS ⟨x, hx⟩).2

theorem sig_alg (σ : E →ₐ[F] E) (b : Fv F v) :
    sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) b) = algebraMap (Fv F v) (Fv F v ⊗[F] E) b := by
  rw [Algebra.algebraMap_eq_smul_one, sigR_smul, map_one]

theorem hR_mem (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) {x y : Fin M → Fv F v ⊗[F] E}
    (hx : ∀ i, x i ∈ S) (hy : ∀ i, y i ∈ S) : hR (Fv F v) σ J x y ∈ S := by
  unfold hR hform
  refine sum_mem fun i _ => sum_mem fun j _ => mul_mem (mul_mem (sig_mem hG (hx i)) ?_) (hy j)
  exact hG.J_int i j

theorem BR_mem (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) {X Y : Fin n → Fin M → Fv F v ⊗[F] E}
    (hX : X ∈ latV (M := M) (n := n) bs v) (hY : Y ∈ latV (M := M) (n := n) bs v) :
    BR (Fv F v) σ J X Y ∈ v.adicCompletionIntegers F := by
  have hX' := (mem_lat_iff hG X).1 hX
  have hY' := (mem_lat_iff hG Y).1 hY
  exact sum_mem fun a _ => hG.trace_mem (hR_mem hG (hX' a) (hY' a))

theorem BR_single (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (a : Fin n) (i : Fin M)
    (x : Fv F v ⊗[F] E) (Y : Fin n → Fin M → Fv F v ⊗[F] E) :
    BR (Fv F v) σ J (Pi.single a (Pi.single i x)) Y =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E)
        (sigR (Fv F v) σ x * ∑ j, inclR (F := F) (Fv F v) (J i j) * Y a j) := by
  classical
  unfold BR
  rw [Finset.sum_eq_single a]
  · congr 1
    unfold hR hform
    rw [Finset.sum_eq_single i]
    · simp only [Pi.single_eq_same, Finset.mul_sum, mul_assoc]
      rfl
    · intro i' _ hi'
      simp [Pi.single_eq_of_ne hi']
    · simp
  · intro a' _ ha'
    simp [Pi.single_eq_of_ne ha', hR, hform]
  · simp

theorem entry_mem (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) {Y : Fin n → Fin M → Fv F v ⊗[F] E}
    (h : ∀ X ∈ latV (M := M) (n := n) bs v, ψv (BR (Fv F v) σ J X Y) = 1) (a : Fin n) (i : Fin M) :
    (∑ j, inclR (F := F) (Fv F v) (J i j) * Y a j) ∈ S := by
  classical
  set w := ∑ j, inclR (F := F) (Fv F v) (J i j) * Y a j with hw
  refine (hG.trace_dual w).1 fun s hs => ?_
  refine (hG.psi_cond _).1 fun b hb => ?_
  set β := algebraMap (Fv F v) (Fv F v ⊗[F] E) b with hβ
  set x : Fv F v ⊗[F] E := ((σS ⟨s, hs⟩ : S) : Fv F v ⊗[F] E) * β with hx
  have hxS : x ∈ S := mul_mem (σS _).2 (alg_mem hG hb)
  have hsig : sigR (Fv F v) σ x = s * β := by
    rw [hx, map_mul, ← hG.sig (σS ⟨s, hs⟩), hG.quad.inv, hβ, sig_alg]
  have hX : (Pi.single a (Pi.single i x) : Fin n → Fin M → Fv F v ⊗[F] E) ∈
      latV (M := M) (n := n) bs v := by
    rw [mem_lat_iff hG]
    intro a' i'
    by_cases ha : a' = a
    · subst ha
      by_cases hi : i' = i
      · subst hi
        simpa using hxS
      · simp [Pi.single_eq_of_ne hi]
    · simp [Pi.single_eq_of_ne ha]
  have h1 := h _ hX
  rw [BR_single, hsig] at h1
  have e : s * β * w = b • (w * s) := by
    rw [Algebra.smul_def, ← hβ]
    ring
  rw [e, LinearMap.map_smul, smul_eq_mul, mul_comm] at h1
  exact h1

theorem mem_of_dual (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) {Y : Fin n → Fin M → Fv F v ⊗[F] E}
    (h : ∀ X ∈ latV (M := M) (n := n) bs v, ψv (BR (Fv F v) σ J X Y) = 1) :
    Y ∈ latV (M := M) (n := n) bs v := by
  rw [mem_lat_iff hG]
  intro a j
  set Js := matS S J hG.J_int with hJs
  have hdet : IsUnit Js.det := hG.J_unimod.2
  have hinv : Js⁻¹ * Js = 1 := Matrix.nonsing_inv_mul _ hdet
  have hmap : (Js⁻¹).map S.subtype * Js.map S.subtype = 1 := by
    rw [← Matrix.map_mul, hinv, Matrix.map_one _ (map_zero _) (map_one _)]
  have e := congrFun (congrArg (fun m => Matrix.mulVec m (Y a)) hmap) j
  simp only [← Matrix.mulVec_mulVec, Matrix.one_mulVec] at e
  rw [← e]
  show ∑ i, ((Js⁻¹).map S.subtype) j i * ((Js.map S.subtype).mulVec (Y a)) i ∈ S
  refine sum_mem fun i _ => mul_mem (Js⁻¹ j i).2 ?_
  exact entry_mem hG h a i

end Alg

attribute [local instance] finFE isModTopA isTopRingA

theorem volLat : VolLat := by
  intro F E _ _ _ _ _ σ M n d J T bs v ψv S σS ϖ ε hG μv hμ
  haveI : SecondCountableTopology (Fv F v ⊗[F] E) := scA bs v
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (Fin M → Fv F v ⊗[F] E) := Pi.borelSpace
  haveI : BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := Pi.borelSpace
  let L : AddSubgroup (Fin n → Fin M → Fv F v ⊗[F] E) :=
    { carrier := latV (M := M) (n := n) bs v
      zero_mem' := (mem_lat_iff hG _).2 fun a i => S.zero_mem
      add_mem' := fun {X Y} hX hY => (mem_lat_iff hG _).2 fun a i =>
        S.add_mem ((mem_lat_iff hG _).1 hX a i) ((mem_lat_iff hG _).1 hY a i)
      neg_mem' := fun {X} hX => (mem_lat_iff hG _).2 fun a i =>
        S.neg_mem ((mem_lat_iff hG _).1 hX a i) }
  have hdual : ∀ Y, (∀ X ∈ L, ψv (BR (Fv F v) σ J X Y) = 1) ↔ Y ∈ L := by
    intro Y
    refine ⟨fun h => mem_of_dual hG h, fun hY X hX => hG.psi_of_mem (BR_mem hG hX hY)⟩
  show μv (L : Set (Fin n → Fin M → Fv F v ⊗[F] E)) = 1
  refine selfDualVol _ μv (fun X Y => ψv (BR (Fv F v) σ J X Y)) hμ L (isClopen_lat bs v n M).isOpen
    (isCompact_lat bs v n M) ?_ ?_ hdual
  · intro X X' Y
    simp only [BR_add, hG.psi_add]
  · intro Y
    exact hG.psi_cont.comp (continuous_BR v σ J Y)

end GlobalTheory.CompanionTheory.GunrVol

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeVolumeUnramifiedStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.lattice_volume_unramified : PositivityTheory.SiegelWeilFormula.Gunr.VolLat := by
  first | exact @GlobalTheory.CompanionTheory.GunrVol.volLat | exact GlobalTheory.CompanionTheory.GunrVol.volLat | (intros; apply GlobalTheory.CompanionTheory.GunrVol.volLat <;> assumption)
end
end
