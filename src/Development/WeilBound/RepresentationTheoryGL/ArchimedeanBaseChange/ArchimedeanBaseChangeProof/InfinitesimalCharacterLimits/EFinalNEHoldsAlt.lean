module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.E45FinalGluing
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
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.EtaleBaseChangeOfDuality
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.ContinuousAdmissibleReps.AdmissibleDiscreteSpaces
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TensorOperatorTrees.TreeLemmas
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TwistLimitStatement.Lim5
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasInfCharGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivSplitCentre
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeSpehOfDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InfinitesimalCharacterInduced
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieCentralElementTrace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceOperatorEigenvalueSum
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.CasimirOnParabolicInduction
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AutomorphicNormFiniteNonzeroStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFundamentalDomainGLStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelSumBoundUniformStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrthogonalOfNonIsomorphicStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TypedSpaceApproximation
import Mathlib.Tactic.ENatToNat
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.SeparationHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LimitPairSpaces.MulMemPairSpace

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.E45FinalGluingStatement

section

@[expose] public section

open scoped Classical
namespace PositivityTheory.Rg.BcB.SpectralAccumulation

theorem _root_.GlobalTheory.T.e45_final_gluing : PositivityTheory.Rg.BcB.SpectralAccumulation.InfinitesimalCharacterGlue := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.eFinalGlue | exact GlobalTheory.CompanionTheory.EGlue.eFinalGlue | (intros; apply GlobalTheory.CompanionTheory.EGlue.eFinalGlue <;> assumption)
end SpectralAccumulation
end BcB
end Rg
end PositivityTheory
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.UntwistedCharacters.HasInfCharGLTopZero

section

@[expose] public section

noncomputable section

open scoped Classical
open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Untw

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem hasInfCharGL_mono {N : ℕ} {V W : Submodule ℂ (Sm E N)} {τ : E →+* ℂ} {m : Multiset ℂ}
    (h : HasInfCharGL V τ m) (hle : W ≤ V) : HasInfCharGL W τ m :=
  ⟨h.1, fun u φ hφ => h.2 u φ (hle hφ)⟩

theorem hasInfCharGL_tw {N : ℕ} {V : Submodule ℂ (Sm E N)} {τ : E →+* ℂ} {m : Multiset ℂ}
    (h : HasInfCharGL V τ m) (z : ℂ) : HasInfCharGL (tw V z) τ (m.map (· + z)) := by
  have hW := GlobalTheory.NormIndCap.hasInfCharGL_map_mulChi h (GlobalTheory.CuspRep.Model.absC E z)
  rw [GlobalTheory.CuspRep.Model.expo_absC] at hW
  exact hW

theorem prod_cancel (m₁ m₂ : Multiset ℂ) (u : ℂ) (r s : ℕ) :
    ((m₁.map (· + (s : ℂ) / 2)).map (u - (s : ℂ) / 2 + ·)).prod *
        ((m₂.map (· + -(r : ℂ) / 2)).map (u + (r : ℂ) / 2 + ·)).prod = ((m₁ + m₂).map (u + ·)).prod := by
  rw [Multiset.map_add (f := _), Multiset.prod_add, Multiset.map_map, Multiset.map_map]
  congr 2
  · exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp_apply]; ring
  · exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp_apply]; ring

theorem hasInfCharGL_node {r s : ℕ} {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {τ : E →+* ℂ}
    {m₁ m₂ : Multiset ℂ} (h₁ : HasInfCharGL U₁ τ m₁) (h₂ : HasInfCharGL U₂ τ m₂) :
    HasInfCharGL (Submodule.span ℂ {φ | MemInd2 (tw U₁ ((s : ℂ) / 2)) (tw U₂ (-(r : ℂ) / 2)) φ}) τ (m₁ + m₂) := by
  refine ⟨by rw [Multiset.card_add, h₁.1, h₂.1], fun u φ hφ => ?_⟩
  induction hφ using Submodule.span_induction with
  | mem F hF =>
    have hc : cap τ u F = (((m₁.map (· + (s : ℂ) / 2)).map (u - (s : ℂ) / 2 + ·)).prod *
        ((m₂.map (· + -(r : ℂ) / 2)).map (u + (r : ℂ) / 2 + ·)).prod) • F :=
      PositivityTheory.Rg.Rs.PInfInd2A.casimir_on_parabolic_induction (n := ![r, s]) (tw U₁ ((s : ℂ) / 2)) (tw U₂ (-(r : ℂ) / 2)) τ _ _
        (hasInfCharGL_tw h₁ _) (hasInfCharGL_tw h₂ _) u F hF
    rw [hc, prod_cancel]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul a x _ hx => rw [map_smul, hx, smul_comm]

theorem hasInfCharGL_space {N : ℕ} (t : Tr E N) (τ : E →+* ℂ) (m : Multiset ℂ) (h : t.InfOf τ m) :
    HasInfCharGL t.space τ m := by
  induction t generalizing m with
  | leaf V z =>
    obtain ⟨m₀, h₀, rfl⟩ := h
    exact hasInfCharGL_tw h₀ z
  | @node r s t₁ t₂ ih₁ ih₂ =>
    obtain ⟨m₁, m₂, h₁, h₂, rfl⟩ := h
    refine hasInfCharGL_mono (hasInfCharGL_node (ih₁ m₁ h₁) (ih₂ m₂ h₂)) ?_
    rw [Tr.space]
    exact Submodule.span_mono fun φ hφ => hφ.1

theorem hasInfCharGL_top_zero (τ : E →+* ℂ) : HasInfCharGL (⊤ : Submodule ℂ (Sm E 0)) τ 0 := by
  refine ⟨rfl, fun u φ _ => ?_⟩
  simp [cap, Formalism.REAL.qdet, Formalism.REAL.qminor]

theorem exists_infOf {N : ℕ} (t : Tr E N) (ht : t.Good) (τ : E →+* ℂ) : ∃ m, t.InfOf τ m := by
  induction t with
  | leaf V z =>
    rcases ht with ⟨rfl, rfl, rfl⟩ | ⟨_, hV, _⟩
    · exact ⟨0, 0, hasInfCharGL_top_zero τ, by simp⟩
    · obtain ⟨m₀, h₀⟩ := GlobalTheory.ResW.IrrInfChar.exists_hasInfCharGL hV τ
      exact ⟨_, m₀, h₀, rfl⟩
  | node t₁ t₂ ih₁ ih₂ =>
    obtain ⟨m₁, h₁⟩ := ih₁ ht.1
    obtain ⟨m₂, h₂⟩ := ih₂ ht.2
    exact ⟨_, m₁, m₂, h₁, h₂, rfl⟩

theorem trace_eq {N : ℕ} {V : Submodule ℂ (Sm E N)} {τ : E →+* ℂ} {m : Multiset ℂ} (hm : HasInfCharGL V τ m) :
    ∀ φ ∈ V, (∑ i : Fin N, Eop τ i i) φ = m.sum • φ := by
  intro φ hφ
  obtain ⟨hc, hu⟩ := hm
  rcases N with _ | n
  · obtain rfl : m = 0 := Multiset.card_eq_zero.1 hc
    simp
  · obtain ⟨l, rfl⟩ := Quot.exists_rep m
    refine GlobalTheory.CompanionTheory.CapelliTrace.trace_of_qdet (Eop τ) l (by simpa using hc) φ fun v => ?_
    have := hu (v - (n : ℂ) / 2) φ hφ
    rw [cap, show v - (n : ℂ) / 2 + (((n + 1 : ℕ) : ℂ) - 1) / 2 = v by push_cast; ring] at this
    simpa using this

theorem lie_oneL_eq_zero {N : ℕ} (φ : Sm E N) (h : ∀ t g, φ.1 (splitCentre E N t * g) = φ.1 g) :
    lie E N (oneL E N) φ = 0 := by
  refine Subtype.ext (funext fun g => ?_)
  have h1 := GlobalTheory.CuspRep.SplitDeriv.hasDerivAt_splitCentre φ g 0
  have h2 : (fun t : ℝ => φ.1 (g * splitCentre E N t)) = fun _ => φ.1 g := by
    funext t
    rw [← GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm, h]
  rw [h2] at h1
  have h3 := h1.unique (hasDerivAt_const (0 : ℝ) (φ.1 g))
  rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_zero, mul_one] at h3
  exact h3

theorem sum_trace_eq_zero {N : ℕ} {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) (m : (E →+* ℂ) → Multiset ℂ)
    (hm : ∀ τ, HasInfCharGL V τ (m τ)) : ∑ τ, (m τ).sum = 0 := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  have h := lie_oneL_eq_zero φ (hV.sqInt φ hφ).1
  rw [GlobalTheory.CompanionTheory.ClozelLie.lie_oneL_eq_sum_Eop, LinearMap.sum_apply,
    Finset.sum_congr rfl fun τ _ => trace_eq (hm τ) φ hφ, ← Finset.sum_smul] at h
  exact (smul_eq_zero.1 h).resolve_right h0

theorem im_sum_of {s : Multiset ℂ} {c : ℝ} (h : ∀ x ∈ s, x.im = c) :
    s.sum.im = (Multiset.card s : ℝ) * c := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.sum_cons, Complex.add_im, h a (by simp), ih fun x hx => h x (by simp [hx]), Multiset.card_cons]
    push_cast
    ring

theorem twist_eq_zero {N : ℕ} (hN : 0 < N) {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {z : ℂ} (hz : z.re = 0)
    (m : (E →+* ℂ) → Multiset ℂ) (hm : ∀ τ, HasInfCharGL V τ (m τ)) (hr : ∀ τ, ∀ x ∈ m τ, (x + z).im = 0) :
    z = 0 := by
  have h := congrArg Complex.im (sum_trace_eq_zero hV m hm)
  have hτ : ∀ τ, ((m τ).sum).im = (N : ℝ) * (-z.im) := fun τ => by
    rw [im_sum_of (c := -z.im) fun x hx => by
        have := hr τ x hx
        simp only [Complex.add_im] at this
        linarith, (hm τ).1]
  rw [Complex.im_sum, Finset.sum_congr rfl fun τ _ => hτ τ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Complex.zero_im] at h
  have hc : (Fintype.card (E →+* ℂ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have him : z.im = 0 := by
    have := mul_eq_zero.1 h
    rcases this with h1 | h1
    · exact absurd h1 hc
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exact absurd h2 hN'
      · linarith
  exact Complex.ext hz him

theorem untw_of_infOf {N : ℕ} (t : Tr E N) (ht : t.Good) (mf : (E →+* ℂ) → Multiset ℂ)
    (h : ∀ τ, t.InfOf τ (mf τ)) (hr : ∀ τ, ∀ x ∈ mf τ, x.im = 0) : t.Untw := by
  induction t generalizing mf with
  | leaf V z =>
    intro w hw
    simp only [Tr.twists, List.mem_singleton] at hw
    subst hw
    rcases ht with ⟨_, _, hz⟩ | ⟨hN, hV, hz⟩
    · exact hz
    · choose m₀ h₀ he using h
      refine twist_eq_zero hN hV hz m₀ h₀ fun τ x hx => ?_
      exact hr τ (x + w) (by rw [he τ]; exact Multiset.mem_map_of_mem _ hx)
  | node t₁ t₂ ih₁ ih₂ =>
    choose m₁ m₂ h₁ h₂ he using h
    intro w hw
    simp only [Tr.twists, List.mem_append] at hw
    rcases hw with hw | hw
    · exact ih₁ ht.1 m₁ h₁ (fun τ x hx => hr τ x (by rw [he τ]; exact Multiset.mem_add.2 (Or.inl hx))) w hw
    · exact ih₂ ht.2 m₂ h₂ (fun τ x hx => hr τ x (by rw [he τ]; exact Multiset.mem_add.2 (Or.inr hx))) w hw

theorem untwOfReal_holds : UntwOfReal := by
  intro E _ _ _ N t n ht hne hn hrs
  choose mf hmf using exists_infOf t ht
  have heq : ∀ τ, n τ = mf τ := fun τ =>
    GlobalTheory.BcSpehProof.hasInfCharGL_unique hne (hn τ) (hasInfCharGL_space t τ (mf τ) (hmf τ))
  exact untw_of_infOf t ht mf hmf fun τ x hx => (hrs τ).1 x (heq τ ▸ hx)

end PositivityTheory.Rg.BcB.SpectralAccumulation.Untw

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.EFinalOf

section

@[expose] public section

namespace PositivityTheory.Rg.BcB.SpectralAccumulation

theorem eFinal_of (hS : Sep4) (hF : FinDisc) (hL : LimVec) : EFinal :=
  (GlobalTheory.T.e45_final_gluing : InfinitesimalCharacterGlue) PositivityTheory.Rg.BcB.E.E3.etale_base_change_of_duality hS (LimG.lim5 hF) Trees.treeLemmas.2.2.1 Trees.treeLemmas.2.1
    Trees.treeLemmas.1 hL admissible_discrete_spaces Untw.untwOfReal_holds Trees.treeLemmas.2.2.2

end PositivityTheory.Rg.BcB.SpectralAccumulation
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.IsometrySymmetry.IsoVSymm

section

@[expose] public section

open scoped Classical
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

noncomputable section

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.FiniteDiscreteTypes

theorem isoV_symm {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} {V V' : Submodule ℂ (Sm E N)}
    (hV : _root_.GlobalTheory.CuspRep.IsStable V) (h : IsoV V V') : IsoV V' V := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T.symm, fun o φ ψ e => ?_⟩
  have hm : act o (T.symm φ).1 ∈ V := hV o _ (T.symm φ).2
  have h1 := hT o (T.symm φ) ⟨_, hm⟩ rfl
  rw [LinearEquiv.apply_symm_apply, ← e] at h1
  have h2 : T ⟨_, hm⟩ = ψ := Subtype.ext h1
  rw [← h2, LinearEquiv.symm_apply_apply]

theorem finDisc : FinDisc := by
  intro E _ _ _ N _ _ μ _ K W R ε hK hW hε hRep
  set D : Submodule ℂ (Sm E N) → Prop := fun V => IsDiscrete V ∧ HasType K W V ∧ InfBdd R V ∧
    ∀ r, 0 < r → r < N → ∀ c ∈ ExpV r V, pE E N r c ≤ -ε * (r * ((N : ℝ) - r)) with hD
  by_cases hne : ∃ V, D V
  swap
  · exact ⟨∅, fun V h1 h2 h3 h4 => (hne ⟨V, h1, h2, h3, h4⟩).elim⟩
  obtain ⟨V₁, h₁⟩ := hne
  obtain ⟨F, hF⟩ := GlobalTheory.T.exists_fundamental_domain_GL E N μ _ (h₁.1.sqInt 0 (zero_mem _))
  obtain ⟨α, δ, hαc, hαs, hδ, hα⟩ := hRep
  obtain ⟨Ω, hΩ, hconc⟩ := GlobalTheory.CompanionTheory.Conc.conc E N μ K W R ε δ α F hK hW hε hαc hαs hδ hF
  obtain ⟨B, hB, hbes⟩ := GlobalTheory.T.kernel_sum_bound_uniform E N μ δ α F Ω hαc hαs hδ hF hΩ

  have key : ∀ (n : ℕ) (Vs : Fin n → Submodule ℂ (Sm E N)), (∀ i, D (Vs i)) →
      (∀ i j, i ≠ j → ¬ IsoV (Vs i) (Vs j)) → (n : ENNReal) ≤ 2 * B := by
    intro n Vs hVs hne
    have hsel : ∀ i, ∃ ψ : Sm E N, ψ ∈ Vs i ∧ TypeB K W ψ ∧ (∫⁻ x in F, ‖ψ.1 x‖ₑ ^ 2 ∂μ) = 1 := by
      intro i
      obtain ⟨hd, ⟨φ, hφ, h0, hty⟩, -, -⟩ := hVs i
      obtain ⟨hT, hZ⟩ := GlobalTheory.T.automorphic_norm_finite_nonzero E N μ F hF φ (hd.aut φ hφ) (hd.sqInt φ hφ) h0
      set L := ∫⁻ x in F, ‖φ.1 x‖ₑ ^ 2 ∂μ with hL
      have hLr : 0 < L.toReal := ENNReal.toReal_pos hZ hT
      set c : ℝ := (Real.sqrt L.toReal)⁻¹ with hc
      have hc0 : 0 < c := inv_pos.2 (Real.sqrt_pos.2 hLr)
      refine ⟨(c : ℂ) • φ, (Vs i).smul_mem _ hφ, ⟨fun u hu g => ?_, fun g => ?_⟩, ?_⟩
      · have := hty.1 u hu g
        simp only [Submodule.coe_smul, Pi.smul_apply, this]
      · exact W.smul_mem (c : ℂ) (hty.2 g)
      · have e : ∀ x, ‖(((c : ℂ) • φ : Sm E N)).1 x‖ₑ ^ 2 = ENNReal.ofReal (c ^ 2) * ‖φ.1 x‖ₑ ^ 2 := by
          intro x
          have h2 : ((((c : ℂ) • φ : Sm E N)).1 x) = (c : ℂ) * φ.1 x := rfl
          rw [h2, enorm_mul, mul_pow]
          congr 1
          rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0,
            ENNReal.ofReal_pow hc0.le]
        simp only [e]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← hL]
        have : c ^ 2 = (L.toReal)⁻¹ := by
          rw [hc, inv_pow, Real.sq_sqrt hLr.le]
        rw [this, ENNReal.ofReal_inv_of_pos hLr, ENNReal.ofReal_toReal hT]
        exact ENNReal.inv_mul_cancel hZ hT
    choose ψ hψV hψT hψ1 using hsel
    have hcont : ∀ i, Continuous (ψ i).1 := fun i =>
      ContAut.continuous_of_isOpen_stab E N (ψ i) ((hVs i).1.aut _ (hψV i)).level
    have hleft : ∀ i, ∀ γ ∈ latticeGL E N, ∀ x, (ψ i).1 (γ * x) = (ψ i).1 x := by
      intro i γ hγ x
      obtain ⟨ρ, m, rfl⟩ := GlobalTheory.CuspRep.CuspidalL2GL.mem_latticeGL_iff.1 hγ
      have h1 := ((hVs i).1.sqInt _ (hψV i)).1
      rw [mul_assoc, ((hVs i).1.aut _ (hψV i)).left, ← GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_intCast, h1]
    have hs : ∀ i, ∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * (ψ i).1 (x * y) ∂μ = s * (ψ i).1 x := by
      intro i
      refine hα (ψ i) ((hVs i).1.aut _ (hψV i)) (hψT i) fun τ => ?_
      obtain ⟨m, hm, hb⟩ := (hVs i).2.2.1 τ
      refine ⟨m, ⟨hm.1, fun u φ hφ => ?_⟩, hb⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
      rw [map_smul, hm.2 u _ (hψV i), smul_comm]
    have hcB := hbes n (fun i => (ψ i).1) hcont hleft hs hψ1 (fun i j hij =>
      GlobalTheory.T.orthogonal_of_non_isomorphic E N μ F hF (Vs i) (Vs j) (hVs i).1 (hVs j).1 (hne i j hij) _ (hψV i) _ (hψV j))
    have h1 : ∀ i, 1 ≤ 2 * ∫⁻ x in Ω, ‖(ψ i).1 x‖ₑ ^ 2 ∂μ := fun i =>
      hconc (Vs i) (ψ i) (hVs i).1 (hψV i) (hψT i) (hVs i).2.2.1 (hVs i).2.2.2 (hs i) (hψ1 i)
    calc (n : ENNReal) = ∑ _i : Fin n, (1 : ENNReal) := by simp
      _ ≤ ∑ i : Fin n, 2 * ∫⁻ x in Ω, ‖(ψ i).1 x‖ₑ ^ 2 ∂μ := Finset.sum_le_sum fun i _ => h1 i
      _ = 2 * ∑ i : Fin n, ∫⁻ x in Ω, ‖(ψ i).1 x‖ₑ ^ 2 ∂μ := by rw [Finset.mul_sum]
      _ ≤ 2 * B := by gcongr
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, 2 * B ≤ (n₀ : ENNReal) := by
    have h2B : 2 * B ≠ ⊤ := ENNReal.mul_ne_top (by simp) hB
    exact ENNReal.exists_nat_gt h2B |>.imp fun _ h => h.le
  set P : ℕ → Prop := fun n => ∃ Vs : Fin n → Submodule ℂ (Sm E N), (∀ i, D (Vs i)) ∧
    ∀ i j, i ≠ j → ¬ IsoV (Vs i) (Vs j) with hP
  have hbd : ∀ n, P n → n ≤ n₀ := by
    rintro n ⟨Vs, h1, h2⟩
    exact_mod_cast (key n Vs h1 h2).trans hn₀
  have hP0 : P 0 := ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  set n := Nat.findGreatest P n₀ with hn
  obtain ⟨Vs, hVs, hpw⟩ : P n := Nat.findGreatest_spec (P := P) (Nat.zero_le _) hP0
  refine ⟨Finset.univ.image Vs, fun V h1 h2 h3 h4 => ?_⟩
  by_contra hno
  have hDV : D V := ⟨h1, h2, h3, h4⟩
  have hno' : ∀ i, ¬ IsoV V (Vs i) := fun i hi => hno ⟨Vs i, Finset.mem_image_of_mem _ (Finset.mem_univ i), hi⟩
  have hnext : P (n + 1) := by
    refine ⟨Fin.cons V Vs, fun i => ?_, fun i j hij => ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hDV
      · simpa using hVs i
    · induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j => simpa using hno' j
      | succ i =>
        induction j using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          exact fun h => hno' i (isoV_symm (hVs i).1.stable h)
        | succ j =>
          simpa using hpw i j fun e => hij (by rw [e])
  have := Nat.le_findGreatest (hbd _ hnext) hnext
  omega

end PositivityTheory.Rg.BcB.SpectralAccumulation.FiniteDiscreteTypes

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.EFinalNEHoldsAlt

section

@[expose] public section

namespace PositivityTheory.Rg.BcB.SpectralAccumulation

theorem eFinal_holds' : EFinal := eFinal_of Cz.separation_holds FiniteDiscreteTypes.finDisc LV.limVec

end PositivityTheory.Rg.BcB.SpectralAccumulation
end
end
