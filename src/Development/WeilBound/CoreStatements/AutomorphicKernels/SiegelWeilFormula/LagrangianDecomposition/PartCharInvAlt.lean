module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.PartCharInv
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.FinPart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenSeparating
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqMulApplyZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceFormMapSurjective
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.KillsLinearMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SbSlice

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

namespace PositivityTheory.SiegelWeilFormula.Ald.PCI

variable {F : Type} [Field F] [NumberField F]

theorem exists_slice {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {κ' κ'' : Type} [Fintype κ'] [Fintype κ'']
    (f : SchwartzMap (κ' ⊕ κ'' → W) ℂ) :
    ∃ f' : SchwartzMap (κ' → W) ℂ, ∀ v, f' v = f (Sum.elim v 0) := by
  let ι : (κ' → W) →L[ℝ] (κ' ⊕ κ'' → W) := ContinuousLinearMap.pi fun j =>
    Sum.elim (fun i => ContinuousLinearMap.proj i) (fun _ => 0) j
  have hι : ∀ v, ι v = Sum.elim v 0 := fun v => by funext j; rcases j with j | j <;> rfl
  have hn : ∀ v, ‖v‖ ≤ ‖ι v‖ := fun v => by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    have := norm_le_pi_norm (ι v) (Sum.inl i)
    rw [hι] at this ⊢
    simpa using this
  refine ⟨SchwartzMap.compCLM ℂ (g := ι) ι.hasTemperateGrowth ⟨1, 1, fun v => ?_⟩ f, fun v => ?_⟩
  · rw [one_mul, pow_one]; linarith [hn v]
  · simp [hι]

theorem sb_slice {X : Type} [TopologicalSpace X] [Zero X] [T2Space X] {κ' κ'' : Type}
    {g : (κ' ⊕ κ'' → X) → ℂ} (hg : g ∈ SB (κ' ⊕ κ'' → X)) : (fun z : κ' → X => g (Sum.elim z 0)) ∈ SB (κ' → X) := by
  have hc : Continuous fun z : κ' → X => (Sum.elim z 0 : κ' ⊕ κ'' → X) := by
    refine continuous_pi fun j => ?_
    rcases j with j | j
    · exact continuous_apply j
    · exact continuous_const
  refine ⟨hg.1.comp_continuous hc, ?_⟩
  have hK : IsCompact ((fun x : κ' ⊕ κ'' → X => x ∘ Sum.inl) '' tsupport g) :=
    hg.2.isCompact.image (continuous_pi fun i => continuous_apply _)
  refine HasCompactSupport.intro' hK hK.isClosed fun z hz => ?_
  by_contra hne
  apply hz
  exact ⟨Sum.elim z 0, subset_tsupport _ hne, rfl⟩

end PositivityTheory.SiegelWeilFormula.Ald.PCI

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.PartCharInvOf

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

namespace PositivityTheory.SiegelWeilFormula.Ald.PCI

theorem partCharInv_of (hfin : FinPart) : PartCharInv := by
  intro F _ _ ψ hψ κ' κ'' _ _ l hl hinv Ψ hΨ hzero
  classical
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.CharInvForm.exists_schwartz_one (κ'' → mixedEmbedding.mixedSpace F)
  obtain ⟨U₀, hU₀o, hU₀c, -, -⟩ := GlobalTheory.FinSepChar.finite_chars_separate F ψ hψ κ'' Set.univ Filter.univ_mem
  set θf : (κ'' → Af F) → ℂ := GlobalTheory.CharForm.cosetInd U₀ 0 with hθf
  have hθfSB : θf ∈ SB (κ'' → Af F) := GlobalTheory.CharForm.cosetInd_mem_SB U₀ hU₀o hU₀c 0
  have hθf0 : θf 0 = 1 := by simp [hθf, GlobalTheory.CharForm.cosetInd]
  set θ : (κ'' → AF F) → ℂ := pureA F f₀ θf with hθ
  let P : ((κ' ⊕ κ'' → AF F) → ℂ) →ₗ[ℂ] ((κ' ⊕ κ'' → AF F) → ℂ) :=
    { toFun := fun Φ x => Φ (Sum.elim (x ∘ Sum.inl) 0) * θ (x ∘ Sum.inr)
      map_add' := fun _ _ => by funext x; simp [add_mul]
      map_smul' := fun _ _ => by funext x; simp [mul_assoc] }
  have hP : ∀ Φ x, P Φ x = Φ (Sum.elim (x ∘ Sum.inl) 0) * θ (x ∘ Sum.inr) := fun _ _ => rfl
  have e1 : ∀ x : κ' ⊕ κ'' → AF F, (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((Sum.elim (x ∘ Sum.inl) 0 : κ' ⊕ κ'' → AF F) i).1) =
      Sum.elim ((fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) ∘ Sum.inl) 0 := by
    intro x; funext j; rcases j with j | j
    · rfl
    · simp only [Sum.elim_inr, Pi.zero_apply]
      exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have e2 : ∀ x : κ' ⊕ κ'' → AF F, (fun i => ((Sum.elim (x ∘ Sum.inl) 0 : κ' ⊕ κ'' → AF F) i).2) =
      Sum.elim ((fun i => (x i).2) ∘ Sum.inl) 0 := by
    intro x; funext j; rcases j with j | j <;> rfl
  have gen : ∀ (f : SchwartzMap (κ' ⊕ κ'' → mixedEmbedding.mixedSpace F) ℂ) (g : (κ' ⊕ κ'' → Af F) → ℂ),
      g ∈ SB (κ' ⊕ κ'' → Af F) → l (pureA F f g) = l (P (pureA F f g)) := by
    intro f g hg
    obtain ⟨fs, hfs⟩ := exists_slice (κ'' := κ'') f
    obtain ⟨f₁, hf₁⟩ := GlobalTheory.SchwartzBox.exists_schwartz_box fs f₀
    set g₁ : (κ' ⊕ κ'' → Af F) → ℂ := fun z => g (Sum.elim (z ∘ Sum.inl) 0) * θf (z ∘ Sum.inr) with hg₁def
    have hg₁ : g₁ ∈ SB (κ' ⊕ κ'' → Af F) := GlobalTheory.SchwartzBox.sb_box (sb_slice hg) hθfSB
    have hPf : P (pureA F f g) = pureA F f₁ g₁ := by
      funext x
      rw [hP]
      simp only [pureA, hθ, hf₁, hfs, hg₁def]
      rw [e1 x, e2 x]
      simp only [Function.comp_def]
      ring
    rw [hPf]
    obtain ⟨T, hT⟩ := hl g hg
    have hA : T f = T f₁ := by
      have h := arch_part T (fun L f₂ f₃ h23 => by
        obtain ⟨Y, hY⟩ := GlobalTheory.TraceDual.exists_trace_rep F κ'' L
        rw [← hT, ← hT, ← hinv (fun i => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Y i)) 0)
          (pureA F f₂ g) (GlobalTheory.CharInvForm.mem_schA f₂ hg)]
        congr 1
        funext x
        simp only [pureA, h23, GlobalTheory.CharInvForm.psi_dot_inf hψ, hY, Function.comp_def, mul_assoc]) (f - f₁) (fun v hv => by
          have hv' : v = Sum.elim (v ∘ Sum.inl) 0 := by
            funext j; rcases j with j | j
            · rfl
            · exact congrFun hv j
          rw [SchwartzMap.sub_apply, hf₁, hfs, hv, hf₀, mul_one]
          rw [← hv', sub_self])
      rw [map_sub, sub_eq_zero] at h
      exact h
    let a : ((κ' ⊕ κ'' → Af F) → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun h => l (pureA F f₁ h)
        map_add' := fun h h' => by
          rw [← map_add (f := _)]
          congr 1
          funext x
          simp [pureA, add_mul, mul_assoc, mul_comm, mul_left_comm]
        map_smul' := fun s h => by
          rw [RingHom.id_apply, ← map_smul]
          congr 1
          funext x
          simp [pureA, add_mul, mul_assoc, mul_comm, mul_left_comm] }
    have hB : a g = a g₁ := by
      have h := hfin F ψ hψ κ' κ'' a (fun y h hh => by
        show l (pureA F f₁ _) = l (pureA F f₁ h)
        rw [← hinv (fun i => pairA F 0 (y i)) (pureA F f₁ h) (GlobalTheory.CharInvForm.mem_schA f₁ hh)]
        congr 1
        funext x
        simp [pureA, GlobalTheory.CharInvForm.dot_pairA_fin, Function.comp_def, mul_left_comm]) (g - g₁) (sub_mem hg hg₁) (fun z' => by
          simp only [Pi.sub_apply, hg₁def, Sum.elim_comp_inl, Sum.elim_comp_inr, hθf0, mul_one, sub_self])
      rw [map_sub, sub_eq_zero] at h
      exact h
    calc l (pureA F f g) = T f := hT f
      _ = T f₁ := hA
      _ = l (pureA F f₁ g) := (hT f₁).symm
      _ = a g := rfl
      _ = a g₁ := hB
      _ = l (pureA F f₁ g₁) := rfl
  have key : ∀ Φ ∈ schA F (κ' ⊕ κ''), l Φ = l (P Φ) := by
    intro Φ hΦ
    induction hΦ using Submodule.span_induction with
    | mem Φ hmem =>
      obtain ⟨f, g, hg, rfl⟩ := hmem
      exact gen f g hg
    | zero => simp
    | add _ _ _ _ h h' => rw [map_add (f := _), map_add (f := _), map_add (f := _), h, h']
    | smul c _ _ h => rw [map_smul, map_smul, map_smul, h]
  have h0 : P Ψ = 0 := by
    funext x
    rw [hP, hzero, zero_mul]
    rfl
  rw [key Ψ hΨ, h0, map_zero]

end PositivityTheory.SiegelWeilFormula.Ald.PCI

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SplitPoint

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

namespace PositivityTheory.SiegelWeilFormula.Ald.PCI

def sndHom (κ' κ'' A : Type) [AddCommGroup A] : (κ' ⊕ κ'' → A) →+ (κ'' → A) where
  toFun x := x ∘ Sum.inr
  map_zero' := rfl
  map_add' _ _ := rfl

theorem split_point {κ' κ'' A : Type} [AddCommGroup A] (x : κ' ⊕ κ'' → A) :
    x = Sum.elim (x ∘ Sum.inl) (0 : κ'' → A) + Sum.elim (0 : κ' → A) (x ∘ Sum.inr) := by
  funext i
  rcases i with i | i <;> simp

theorem finPart : FinPart := by
  intro F _ _ ψ hψ κ' κ'' _ _ a ha g hg hg0

  have H : ∀ N ∈ nhds (0 : κ' ⊕ κ'' → Af F), ∃ U : AddSubgroup (κ' ⊕ κ'' → Af F),
      IsOpen (U : Set (κ' ⊕ κ'' → Af F)) ∧ IsCompact (U : Set (κ' ⊕ κ'' → Af F)) ∧ (U : Set _) ⊆ N ∧
      ∀ x₀ ∉ U, ∃ χ ∈ {χ : (κ' ⊕ κ'' → Af F) → ℂ | ∃ y : κ' ⊕ κ'' → Af F, χ = fun x => ψ (pairA F 0 (x ⬝ᵥ y))},
        (∀ u ∈ U, χ (x₀ + u) = χ x₀) ∧ χ x₀ ≠ 1 := by
    intro N hN
    obtain ⟨U, hUo, hUc, hUN, hsep⟩ := GlobalTheory.FinSepChar.finite_chars_separate F ψ hψ (κ' ⊕ κ'') N hN
    refine ⟨U, hUo, hUc, hUN, fun x₀ hx₀ => ?_⟩
    obtain ⟨y, hyU, hy⟩ := hsep x₀ hx₀
    refine ⟨_, ⟨y, rfl⟩, fun u hu => ?_, hy⟩
    show ψ (pairA F 0 ((x₀ + u) ⬝ᵥ y)) = ψ (pairA F 0 (x₀ ⬝ᵥ y))
    rw [add_dotProduct, GlobalTheory.CharInvForm.pairA_zero_add, AddChar.map_add_eq_mul, hyU u hu, mul_one]

  obtain ⟨U₀, hU₀o, hU₀c, -, -, hper⟩ := GlobalTheory.CharForm.exists_periodic H hg Filter.univ_mem

  have hN'' : {u'' : κ'' → Af F | Sum.elim (0 : κ' → Af F) u'' ∈ U₀} ∈ nhds (0 : κ'' → Af F) := by
    have hc : Continuous fun u'' : κ'' → Af F => (Sum.elim (0 : κ' → Af F) u'' : κ' ⊕ κ'' → Af F) :=
      continuous_pi fun i => by rcases i with i | i <;> simp [continuous_const, continuous_apply]
    refine (hU₀o.preimage hc).mem_nhds ?_
    have : (Sum.elim (0 : κ' → Af F) (0 : κ'' → Af F) : κ' ⊕ κ'' → Af F) = 0 := by
      funext i; rcases i with i | i <;> rfl
    show Sum.elim (0 : κ' → Af F) (0 : κ'' → Af F) ∈ U₀
    rw [this]; exact U₀.zero_mem
  obtain ⟨U'', hU''o, -, hU''N, hsep''⟩ := GlobalTheory.FinSepChar.finite_chars_separate F ψ hψ κ'' _ hN''

  have hsc : Continuous (sndHom κ' κ'' (Af F)) := continuous_pi fun i => continuous_apply _
  set W : AddSubgroup (κ' ⊕ κ'' → Af F) := U''.comap (sndHom κ' κ'' (Af F)) with hW
  have hWo : IsOpen (W : Set (κ' ⊕ κ'' → Af F)) := hU''o.preimage hsc
  set P : AddSubgroup (κ' ⊕ κ'' → Af F) := U₀ ⊓ W with hP
  have hPo : IsOpen (P : Set (κ' ⊕ κ'' → Af F)) := by
    rw [hP, AddSubgroup.coe_inf]; exact hU₀o.inter hWo
  have hPc : IsCompact (P : Set (κ' ⊕ κ'' → Af F)) := by
    rw [hP, AddSubgroup.coe_inf]; exact hU₀c.inter_right (AddSubgroup.isClosed_of_isOpen W hWo)
  have hperP : ∀ x, ∀ u ∈ P, g (x + u) = g x := fun x u hu => hper x u (AddSubgroup.mem_inf.mp hu).1

  have : DiscreteTopology ((κ' ⊕ κ'' → Af F) ⧸ P) := QuotientAddGroup.discreteTopology hPo
  have hout : ∀ x : κ' ⊕ κ'' → Af F, g ((x : (κ' ⊕ κ'' → Af F) ⧸ P).out) = g x := fun x => by
    obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add P x
    rw [hh]; exact hperP x h h.2
  have hfin : (QuotientAddGroup.mk '' tsupport g : Set ((κ' ⊕ κ'' → Af F) ⧸ P)).Finite :=
    (hg.2.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete
  set T : Finset ((κ' ⊕ κ'' → Af F) ⧸ P) := hfin.toFinset with hT
  have hsum : g = ∑ q ∈ T, g q.out • GlobalTheory.CharForm.cosetInd P q := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.CharForm.cosetInd, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hx
    · exact (hout x).symm
    · apply image_eq_zero_of_notMem_tsupport
      intro hxs
      exact hx (hfin.mem_toFinset.mpr ⟨x, hxs, rfl⟩)

  have hterm : ∀ q : (κ' ⊕ κ'' → Af F) ⧸ P, g q.out * a (GlobalTheory.CharForm.cosetInd P q) = 0 := by
    intro q
    by_cases hq : q.out ∘ Sum.inr ∈ U''
    · have h0 : g q.out = 0 := by
        rw [split_point q.out, hper _ _ (hU''N hq)]
        exact hg0 _
      rw [h0, zero_mul]
    · obtain ⟨y, hyU, hy⟩ := hsep'' _ hq
      set χ : (κ' ⊕ κ'' → Af F) → ℂ := fun x => ψ (pairA F 0 ((x ∘ Sum.inr) ⬝ᵥ y)) with hχ
      have hmul : (fun x => χ x * GlobalTheory.CharForm.cosetInd P q x) = χ q.out • GlobalTheory.CharForm.cosetInd P q := by
        funext x
        simp only [GlobalTheory.CharForm.cosetInd, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
        split_ifs with hxq
        · have hm : -q.out + x ∈ P := by
            rw [← QuotientAddGroup.out_eq' q] at hxq
            exact QuotientAddGroup.eq.mp hxq.symm
          have hmW : (-q.out + x) ∘ Sum.inr ∈ U'' := (AddSubgroup.mem_inf.mp hm).2
          have hx : x = q.out + (-q.out + x) := by abel
          rw [hx]
          show ψ (pairA F 0 ((q.out ∘ Sum.inr + (-q.out + x) ∘ Sum.inr) ⬝ᵥ y)) = ψ (pairA F 0 ((q.out ∘ Sum.inr) ⬝ᵥ y))
          rw [add_dotProduct, GlobalTheory.CharInvForm.pairA_zero_add, AddChar.map_add_eq_mul, hyU _ hmW, mul_one]
        · rfl
      have e := ha y _ (GlobalTheory.CharForm.cosetInd_mem_SB P hPo hPc q)
      rw [show (fun x => ψ (pairA F 0 ((x ∘ Sum.inr) ⬝ᵥ y)) * GlobalTheory.CharForm.cosetInd P q x) =
        χ q.out • GlobalTheory.CharForm.cosetInd P q from hmul, map_smul, smul_eq_mul] at e
      have : (χ q.out - 1) * a (GlobalTheory.CharForm.cosetInd P q) = 0 := by rw [sub_mul, e, one_mul, sub_self]
      rw [(mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hy), mul_zero]

  rw [hsum, map_sum]
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [map_smul, smul_eq_mul, hterm q]

end PositivityTheory.SiegelWeilFormula.Ald.PCI

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.PartCharInvAlt

section

@[expose] public section

namespace PositivityTheory.SiegelWeilFormula.Ald

theorem partCharInv : PartCharInv := PCI.partCharInv_of PCI.finPart

end PositivityTheory.SiegelWeilFormula.Ald
end
end
