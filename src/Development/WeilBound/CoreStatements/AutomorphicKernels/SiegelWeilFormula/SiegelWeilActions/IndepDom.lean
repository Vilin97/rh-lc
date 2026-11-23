module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.CtSplitOfParts
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.EisLeftInv
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.FirstChernHodgeTateFacts
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContinuousCj
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.IsFirstChernFamily
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
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
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LowerRankDatum
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.MemStabiliserIffFrameLowerBlock
import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldB
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.LocCompactNA

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

set_option linter.unusedSectionVars false

namespace PositivityTheory.SiegelWeilFormula.Act.C1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isClosed_nA (d : SD σ) : IsClosed (nA σ d.Y d.b : Set (Matrix (Fin d.n) (Fin d.n) (AE F E))) := by
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have hc : Continuous (cA σ : AE F E → AE F E) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have e : (nA σ d.Y d.b : Set (Matrix (Fin d.n) (Fin d.n) (AE F E))) =
      {β | βᵀ = -((((ε : ℤ) : AE F E)) • β.map (cA σ))} := Set.ext fun β => kunf.mem_nA_iff hε β
  rw [e]
  exact isClosed_eq continuous_id.matrix_transpose (((continuous_id.matrix_map hc).const_smul (((ε : ℤ) : AE F E))).neg)

instance locCompact_nA (d : SD σ) : LocallyCompactSpace (nA σ d.Y d.b) :=
  haveI : LocallyCompactSpace (Matrix (Fin d.n) (Fin d.n) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin d.n → Fin d.n → AE F E))
  (isClosed_nA d).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem coef_periodic (d : SD σ) {nb : nA σ d.Y d.b → d.G} (hN : IsNMap d.b nb) (φ : d.G → ℂ)
    (hφ : ∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g) (T : nF σ d.Y d.b) (g : d.G) (β₀ : nF σ d.Y d.b)
    (β : nA σ d.Y d.b) :
    φ (nb (β₀ +ᵥ β) * g) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * (β₀ +ᵥ β).1)))) =
      φ (nb β * g) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) := by
  have e1 : (β₀ +ᵥ β : nA σ d.Y d.b) = β₀.1 + β := rfl
  have e2 : ((β₀.1 + β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) (AE F E)) = β₀.1.1 + β.1 := rfl
  rw [e1, kunf.nb_add hN, mul_assoc, hφ _ (kunf.nb_rat hN β₀.2), e2, Matrix.mul_add, Matrix.trace_add, map_add (f := _), neg_add,
    AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, kunf.psi_rat d.ok.good.std T β₀, inv_one, one_mul]

variable {d : SD σ} {L : LD d}

theorem cj_mp {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (h : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
    {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤) {v : Fin L.n → AE F E} (hv : v ∈ L.ratV) :
    MeasurePreserving (cj hU h.1 v) lam lam := by
  have := h.2.1
  refine ⟨(continuous_cj hU h.1 v).measurable, ?_⟩
  have hl := latHaar (nA σ d.Y d.b) lam (nF σ d.Y d.b) (cjE hU h.1 v) (fun x => ⟨fun hx => ?_, fun hx => cj_rat hU h.1 hv hx⟩)
    𝓖 h.2.2.1 (by rw [h.2.2.2]; exact one_ne_zero) (by rw [h.2.2.2]; exact ENNReal.one_ne_top)
  · exact hl
  · have := cj_rat hU h.1 (neg_mem hv) hx
    rwa [show cj hU h.1 (-v) (cjE hU h.1 v x) = x from cj_inv hU h.1 v x] at this

theorem fc_conj {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (h : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
    {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤) (φ : d.G → ℂ) (hφ : ∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g)
    {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T') {u : Fin L.n → AE F E} (hu : u ∈ L.ratV) (g : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * g) = fc d.B.ψ d.b nb lam 𝓖 φ T g := by
  have := h.2.1
  have : VAddInvariantMeasure (nF σ d.Y d.b) (nA σ d.Y d.b) lam := ⟨fun c s _ => measure_preimage_add lam c.1 s⟩
  let H : nA σ d.Y d.b → ℂ := fun β =>
    φ (nb β * g) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))
  have e1 : ∀ β, φ (nb β * (uM u * g)) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) =
      H (cj hU h.1 u β) := by
    intro β
    have e : nb β * (uM u * g) = uM u * (nb (cj hU h.1 u β) * g) := by rw [nb_cj hU h.1 u β]; group
    simp only [H]
    rw [e, hφ _ (uM_rat hU hu), trace_cj hU h.1 hT]
  have hme : MeasurableEmbedding (cj hU h.1 u) := (cjE hU h.1 u).toHomeomorph.measurableEmbedding
  have himg : (cj hU h.1 u) '' 𝓖 = (cj hU h.1 (-u)) ⁻¹' 𝓖 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show cj hU h.1 (-u) (cj hU h.1 u x) ∈ 𝓖
      rwa [cj_inv]
    · intro hy
      refine ⟨cj hU h.1 (-u) y, hy, ?_⟩
      simpa using cj_inv hU h.1 (-u) y
  have hfd : IsAddFundamentalDomain (nF σ d.Y d.b) ((cj hU h.1 (-u)) ⁻¹' 𝓖) lam := by
    refine h.2.2.1.preimage_of_equiv (cj_mp h hU (neg_mem hu)).quasiMeasurePreserving
      (e := fun γ => ⟨cj hU h.1 u γ.1, cj_rat hU h.1 hu γ.2⟩) ⟨fun γ γ' hγ => ?_, fun γ => ?_⟩ fun γ x => ?_
    · have := congrArg (fun y : nF σ d.Y d.b => cj hU h.1 (-u) y.1) hγ
      simp only [cj_inv] at this
      exact Subtype.ext this
    · refine ⟨⟨cj hU h.1 (-u) γ.1, cj_rat hU h.1 (neg_mem hu) γ.2⟩, Subtype.ext ?_⟩
      simpa using cj_inv hU h.1 (-u) γ.1
    · show cj hU h.1 (-u) ((cj hU h.1 u γ.1) + x) = γ.1 + cj hU h.1 (-u) x
      rw [map_add (f := _), cj_inv]
  unfold fc
  simp_rw [e1]
  rw [← (cj_mp h hU hu).setIntegral_image_emb hme H 𝓖, himg,
    hfd.setIntegral_eq h.2.2.1 (fun β₀ β => coef_periodic d h.1 φ hφ T g β₀ β)]

end PositivityTheory.SiegelWeilFormula.Act.C1

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PhzJLeftInv

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ}

theorem range_or (L : LD d) (u : Fin d.n ⊕ Fin d.n) :
    (∃ u', Sum.map L.em L.em u' = u) ∨ u ∈ ({Sum.inl L.i₀, Sum.inr L.i₀} : Set (Fin d.n ⊕ Fin d.n)) := by
  rcases u with a | a <;>
  · by_cases ha : a = L.i₀
    · right; simp [ha]
    · obtain ⟨a', rfl⟩ := (L.rng a).1 ha
      left; first | exact ⟨Sum.inl a', rfl⟩ | exact ⟨Sum.inr a', rfl⟩

theorem j_par (L : LD d) {p : G2 σ L.Y} (hp : p ∈ par2 σ L.Y) : L.j p ∈ par2 σ d.Y := by
  rw [ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame]
  rw [ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block L.sd.ok.frame] at hp
  ext a c
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply]
  rcases range_or L (Sum.inr a) with ⟨u', hu'⟩ | hu
  · rcases range_or L (Sum.inl c) with ⟨v', hv'⟩ | hv
    · rcases u' with a' | a'
      · simp at hu'
      rcases v' with c' | c'
      · have h1 := congrFun (congrFun (L.j_in p) (Sum.inr a')) (Sum.inl c')
        simp only [Matrix.submatrix_apply, Sum.map_inr, Sum.map_inl] at h1
        simp only [Sum.map_inr, Sum.inr.injEq] at hu'
        simp only [Sum.map_inl, Sum.inl.injEq] at hv'
        rw [← hu', ← hv', h1]
        exact congrFun (congrFun hp a') c'
      · simp at hv'
    · rw [(L.j_out p _ hv (Sum.inr a)).2]
      simp
  · rw [(L.j_out p _ hu (Sum.inl c)).1]
    simp

theorem j_rat (L : LD d) {p : G2 σ L.Y} (hp : p ∈ rat2 σ L.Y) : L.j p ∈ rat2 σ d.Y := by
  obtain ⟨g, hg⟩ := hp
  have hm : mat2 p = incM F g.1 := (congrArg Units.val hg).symm
  have hL : inFrame L.b p = incM F ((L.b⁻¹).1 * g.1 * L.b.1) := by
    rw [kunf.incM_mul', kunf.incM_mul', ← hm]; rfl
  let M' := (L.b⁻¹).1 * g.1 * L.b.1
  let M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E := fun u v =>
    if hu : ∃ u', Sum.map L.em L.em u' = u then
      if hv : ∃ v', Sum.map L.em L.em v' = v then M' hu.choose hv.choose else (1 : Matrix _ _ E) u v
    else (1 : Matrix _ _ E) u v
  refine kunf.rat_of_inFrame (b := d.b) (M := M) ?_
  ext u v
  show inFrame d.b (L.j p) u v = inclR (F := F) (AF F) (M u v)
  dsimp only [M]
  by_cases hu : ∃ u', Sum.map L.em L.em u' = u
  · by_cases hv : ∃ v', Sum.map L.em L.em v' = v
    · rw [dite_eq_left hu, dite_eq_left hv]
      have h1 := congrFun (congrFun (L.j_in p) hu.choose) hv.choose
      simp only [Matrix.submatrix_apply, hu.choose_spec, hv.choose_spec] at h1
      rw [h1, hL]
      rfl
    · rw [dite_eq_left hu, dite_eq_right hv]
      have hv' := (range_or L v).resolve_left hv
      rw [(L.j_out p _ hv' u).2]
      simp [Matrix.one_apply, apply_ite]
  · rw [dite_eq_right hu]
    have hu' := (range_or L u).resolve_left hu
    rw [(L.j_out p _ hu' v).1]
    simp [Matrix.one_apply, apply_ite]

theorem phz_j_leftInv (L : LD d) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) (x : d.G) :
    GlobalTheory.AutomorphicL2Unitary.LeftInv (par2 σ L.Y ⊓ rat2 σ L.Y)
      (fun g : G2 σ L.Y => ((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s₁) * f (L.j g * x)) := by
  intro p hp g
  show phz d f s₁ z (L.j (p * g) * x) = phz d f s₁ z (L.j g * x)
  rw [map_mul, mul_assoc]
  exact phz_leftInv d hf z (L.j p) ⟨j_par L hp.1, j_rat L hp.2⟩ _

end PositivityTheory.SiegelWeilFormula.Act.C1

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.IndepDom

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Act

theorem indepDom : IndepDom := by
  intro F E _ _ _ _ _ σ d L s₁ f hf z
  have hE := C1.eis_leftInv d hf z
  refine ⟨fun nb lam 𝓖 𝓖₀ h h₀ uM ν 𝓤 𝓤₀ hU hU₀ T T' hT x => ?_, fun nb' lam' 𝓖' 𝓖'₀ h' h'₀ T' x => ?_⟩
  · have step1 : ∀ g, fc d.B.ψ d.b nb lam 𝓖 (d.eis f s₁ z) T g = fc d.B.ψ d.b nb lam 𝓖₀ (d.eis f s₁ z) T g :=
      fun g => C1.fc_dom d h h₀ _ hE T g
    simp_rw [step1]
    have := hU.2.1
    have : VAddInvariantMeasure L.ratV (Fin L.n → AE F E) ν := ⟨fun c s _ => measure_preimage_add ν c.1 s⟩
    have : Countable L.ratV := by
      have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
      refine Function.Surjective.countable (f := fun v : Fin L.n → E =>
        (⟨GlobalTheory.ThK.incV F v, AddSubgroup.subset_closure ⟨v, rfl⟩⟩ : L.ratV)) fun u => ?_
      obtain ⟨v, hv⟩ := C1.ratV_inc u.2
      exact ⟨v, Subtype.ext hv.symm⟩
    refine hU.2.2.1.setIntegral_eq hU₀.2.2.1 fun u₀ u => ?_
    show fc d.B.ψ d.b nb lam 𝓖₀ (d.eis f s₁ z) T (uM (u₀.1 + u) * x) = fc d.B.ψ d.b nb lam 𝓖₀ (d.eis f s₁ z) T (uM u * x)
    rw [C1.uM_add hU, mul_assoc, C1.fc_conj h₀ hU _ hE hT u₀.2]
  · exact C1.fc_dom L.sd h' h'₀ _ (GlobalTheory.Eis.leftInv_cosetSum (C1.phz_j_leftInv L hf z x)) T' 1

end PositivityTheory.SiegelWeilFormula.Act

end
end
end
