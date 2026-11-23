module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictJoin
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.FinDiscNOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.ContinuousAdmissibleReps.AdmissibleDiscreteSpaces
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.LieInvariants.InvariantOfLieOneLEqZero
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.FixedMonoBo
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar

-- Source module: PositivityTheory.AutomorphicForms.PublishedInputs.BorelInjectivity.EquivariantProjections.ExistsEquivariantProjOfLeSumIrreducible

section

@[expose] public section

open CategoryTheory
open scoped ContDiff Matrix

namespace GlobalTheory.BorelCoh

theorem exists_equivariant_proj_of_le_sum_irreducible {M O : Type} [AddCommGroup M] [Module ℂ M]
    (act : O → Module.End ℂ M) (V : Submodule ℂ M) (hVst : ∀ o, ∀ x ∈ V, act o x ∈ V)
    (hV : V ≤ ⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧
      ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W) :
    ∃ p : M →ₗ[ℂ] M, (∀ o, ∀ x ∈ (⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧
      ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W), p (act o x) = act o (p x)) ∧
      (∀ x, p x ∈ V) ∧ (∀ x ∈ V, p x = x) := by
  set Wt := ⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧
      ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W with hWt
  have hst_sup : ∀ A B : Submodule ℂ M, (∀ o, ∀ x ∈ A, act o x ∈ A) → (∀ o, ∀ x ∈ B, act o x ∈ B) →
      ∀ o, ∀ x ∈ A ⊔ B, act o x ∈ A ⊔ B := by
    intro A B hA hB o x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hA o y hy) (hB o z hz)

  let s : Set (Submodule ℂ M) := {C | (∀ o, ∀ x ∈ C, act o x ∈ C) ∧ C ≤ Wt ∧ Disjoint V C}
  obtain ⟨C, -, ⟨hCst, hCW, hCd⟩, hCmax⟩ := zorn_le_nonempty₀ s (by
    intro c hcs hc y hy
    have hne : c.Nonempty := ⟨y, hy⟩
    have hdir : DirectedOn (· ≤ ·) c := hc.directedOn
    refine ⟨sSup c, ⟨?_, sSup_le fun z hz => (hcs hz).2.1, ?_⟩, fun z hz => le_sSup hz⟩
    · intro o x hx
      obtain ⟨z, hz, hxz⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hx
      exact (Submodule.mem_sSup_of_directed hne hdir).2 ⟨z, hz, (hcs hz).1 o x hxz⟩
    · rw [Submodule.disjoint_def]
      intro x hxV hx
      obtain ⟨z, hz, hxz⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hx
      exact (Submodule.disjoint_def.1 (hcs hz).2.2) x hxV hxz) ⊥
    ⟨fun o x hx => by rw [Submodule.mem_bot] at hx ⊢; rw [hx, map_zero], bot_le, disjoint_bot_right⟩

  have hWle : Wt ≤ V ⊔ C := by
    refine iSup₂_le fun S hS => ?_
    obtain ⟨hSst, hSne, hSmin⟩ := hS
    have hinst : ∀ o, ∀ x ∈ S ⊓ (V ⊔ C), act o x ∈ S ⊓ (V ⊔ C) := fun o x hx =>
      ⟨hSst o x hx.1, hst_sup V C hVst hCst o x hx.2⟩
    rcases hSmin _ inf_le_left hinst with h | h
    · have hSW : S ≤ Wt := le_iSup₂_of_le S ⟨hSst, hSne, hSmin⟩ le_rfl
      have hmem : C ⊔ S ∈ s := ⟨hst_sup C S hCst hSst, sup_le hCW hSW,
        Disjoint.disjoint_sup_right_of_disjoint_sup_left hCd (by rw [disjoint_comm, disjoint_iff]; exact h)⟩
      exact (le_sup_right.trans (hCmax hmem le_sup_left)).trans le_sup_right
    · exact h ▸ inf_le_right
  have hW : Wt = V ⊔ C := le_antisymm hWle (sup_le hV hCW)
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl Wt
  have hc : IsCompl V (C ⊔ D) := by
    constructor
    · exact Disjoint.disjoint_sup_right_of_disjoint_sup_left hCd (hW ▸ hD.disjoint)
    · rw [codisjoint_iff, ← sup_assoc, ← hW, hD.sup_eq_top]
  have hl : ∀ v ∈ V, (V.linearProjOfIsCompl (C ⊔ D) hc v : M) = v := fun v hv =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨v, hv⟩)
  have hr : ∀ w ∈ C ⊔ D, V.linearProjOfIsCompl (C ⊔ D) hc w = 0 := fun w hw =>
    Submodule.linearProjOfIsCompl_apply_right hc ⟨w, hw⟩
  refine ⟨V.subtype ∘ₗ V.linearProjOfIsCompl (C ⊔ D) hc, ?_, fun x => (V.linearProjOfIsCompl _ hc x).2, hl⟩
  intro o x hx
  rw [hW] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  have hz' : z ∈ C ⊔ D := Submodule.mem_sup_left hz
  have hz'' : act o z ∈ C ⊔ D := Submodule.mem_sup_left (hCst o z hz)
  show (V.linearProjOfIsCompl _ hc (act o (y + z)) : M) = act o (V.linearProjOfIsCompl _ hc (y + z))
  rw [map_add (f := _), map_add (f := _), map_add (f := _), hr _ hz'', hr _ hz', add_zero, add_zero, hl _ (hVst o y hy), hl _ hy]

theorem exists_equivariant_proj_of_irreducible_family : ∀ (M O ι : Type) [AddCommGroup M] [Module ℂ M] [Fintype ι] [DecidableEq ι] (act : O → Module.End ℂ M) (V : ι → Submodule ℂ M), (∀ i o, ∀ x ∈ V i, act o x ∈ V i) → (∀ i, V i ≠ ⊥) → (∀ i (W : Submodule ℂ M), W ≤ V i → (∀ o, ∀ x ∈ W, act o x ∈ W) → W = ⊥ ∨ W = V i) → (∀ i j, i ≠ j → ∀ f : M →ₗ[ℂ] M, (∀ o, ∀ x ∈ V i, f (act o x) = act o (f x)) → (∀ x ∈ V i, f x ∈ V j) → ∀ x ∈ V i, f x = 0) → ∀ i, ∃ p : M →ₗ[ℂ] M, (∀ o, ∀ x ∈ (⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧ ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W), p (act o x) = act o (p x)) ∧ (∀ x ∈ (⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧ ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W), p x ∈ V i) ∧ (∀ x ∈ V i, p x = x) ∧ ∀ j, j ≠ i → ∀ x ∈ V j, p x = 0 := by
  intro M O ι _ _ _ _ act V h1 h2 h3 h4 i
  have hirr : ∀ j, V j ≤ (⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧ ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W) := fun j =>
    le_iSup₂_of_le (f := fun (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧
      ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W) => W) (V j) ⟨h1 j, h2 j, h3 j⟩ le_rfl
  obtain ⟨p, hpe, hpV, hpid⟩ := exists_equivariant_proj_of_le_sum_irreducible act (V i) (h1 i) (hirr i)
  exact ⟨p, hpe, fun x _ => hpV x, hpid,
    fun j hji x hx => h4 j i hji p (fun o y hy => hpe o y (hirr j hy)) (fun y _ => hpV y) x hx⟩

end GlobalTheory.BorelCoh
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.FinIso

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.F.F5.Bo.FiniteIsomorphism

open PositivityTheory.Rg.BcB.SpectralAccumulation.AdmDiscPf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem isoV_symm {V V' : Submodule ℂ (Sm E N)} (hV : _root_.GlobalTheory.CuspRep.IsStable V) (h : SpectralAccumulation.IsoV V V') : SpectralAccumulation.IsoV V' V := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T.symm, fun o φ ψ hψ => ?_⟩
  set a := T.symm φ with ha
  let b : V := ⟨act o a.1, hV o a.1 a.2⟩
  have hb : T b = ψ := by
    apply Subtype.ext
    rw [hT o a b rfl, ha, LinearEquiv.apply_symm_apply]
    exact hψ.symm
  rw [← hb, LinearEquiv.symm_apply_apply]

theorem isoV_of_map {V V' : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) (hV' : IsDiscrete V')
    (f : Sm E N →ₗ[ℂ] Sm E N) (hf : ∀ o, ∀ x ∈ V, f (act o x) = act o (f x)) (hfV : ∀ x ∈ V, f x ∈ V')
    (hne : ∃ x ∈ V, f x ≠ 0) : SpectralAccumulation.IsoV V V' := by
  have hker : V ⊓ LinearMap.ker f = ⊥ := by
    rcases hV.irred (V ⊓ LinearMap.ker f) inf_le_left (fun o x hx => Submodule.mem_inf.2 ⟨hV.stable o x (Submodule.mem_inf.1 hx).1,
        LinearMap.mem_ker.2 (by rw [hf o x (Submodule.mem_inf.1 hx).1,
          LinearMap.mem_ker.1 (Submodule.mem_inf.1 hx).2, map_zero])⟩) with h | h
    · exact h
    · exfalso
      obtain ⟨x, hx, hx0⟩ := hne
      have : x ∈ V ⊓ LinearMap.ker f := by rw [h]; exact hx
      exact hx0 (LinearMap.mem_ker.1 (Submodule.mem_inf.1 this).2)
  have himg : V.map f = V' := by
    rcases hV'.irred (V.map f) (Submodule.map_le_iff_le_comap.2 fun x hx => hfV x hx) (fun o y hy => by
        obtain ⟨x, hx, rfl⟩ := hy
        exact ⟨act o x, hV.stable o x hx, hf o x hx⟩) with h | h
    · exfalso
      obtain ⟨x, hx, hx0⟩ := hne
      exact hx0 ((Submodule.mem_bot ℂ).1 (h ▸ Submodule.mem_map_of_mem hx))
    · exact h
  let g : V →ₗ[ℂ] V' := (f.comp V.subtype).codRestrict V' (fun x => hfV x.1 x.2)
  have hinj : Function.Injective g := by
    intro x y hxy
    have h1 : f x.1 = f y.1 := congrArg Subtype.val hxy
    have h2 : x.1 - y.1 ∈ V ⊓ LinearMap.ker f :=
      Submodule.mem_inf.2 ⟨V.sub_mem x.2 y.2, LinearMap.mem_ker.2 (by rw [map_sub, h1, sub_self])⟩
    rw [hker, Submodule.mem_bot, sub_eq_zero] at h2
    exact Subtype.ext h2
  have hsurj : Function.Surjective g := by
    intro y
    have : y.1 ∈ V.map f := himg ▸ y.2
    obtain ⟨x, hx, hxy⟩ := this
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  refine ⟨LinearEquiv.ofBijective g ⟨hinj, hsurj⟩, fun o φ ψ hψ => ?_⟩
  change f ψ.1 = act o (f φ.1)
  rw [hψ, hf o φ.1 φ.2]

theorem linIndep {k : ℕ} (V : Fin k → Submodule ℂ (Sm E N)) (hV : ∀ i, IsDiscrete (V i))
    (hn : ∀ i j, i ≠ j → ¬ SpectralAccumulation.IsoV (V i) (V j)) (φ : Fin k → Sm E N) (hφV : ∀ i, φ i ∈ V i)
    (hφ0 : ∀ i, φ i ≠ 0) : LinearIndependent ℂ φ := by
  classical
  rw [linearIndependent_iff']
  intro s g hs i hi
  obtain ⟨p, -, -, hpid, hp0⟩ := GlobalTheory.BorelCoh.exists_equivariant_proj_of_irreducible_family (Sm E N) (Op E N)
    (Fin k) act V (fun i => (hV i).stable) (fun i => (hV i).ne_bot) (fun i W hW hst => (hV i).irred W hW hst)
    (fun i j hij f hf hfV x hx => by
      by_contra hx0
      exact hn i j hij (isoV_of_map (hV i) (hV j) f hf hfV ⟨x, hx, hx0⟩)) i
  have h := congrArg p hs

  rw [map_sum, map_zero, Finset.sum_eq_single i (fun j _ hji => by rw [map_smul, hp0 j hji _ (hφV j), smul_zero])
  (fun h' => absurd hi h'), map_smul, hpid _ (hφV i)] at h
  exact (smul_eq_zero.1 h).resolve_right (hφ0 i)

theorem mem_forms_of {K : Subgroup (GL (Fin N) (Af E))} {W : Submodule ℂ (Kinf E N → ℂ)}
    {m : (E →+* ℂ) → Multiset ℂ} (hU : ∀ u ∈ rS (lI (W ⊓ contK E N)), ∀ k,
      (fun x => u (x * k)) ∈ rS (lI (W ⊓ contK E N)))
    {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) (hinf : ∀ τ, HasInfCharGL V τ (m τ)) {φ : Sm E N}
    (hφ : φ ∈ V) (hT : SpectralAccumulation.TypeB K W φ) :
    φ ∈ GlobalTheory.Published.AutFinGL.forms K (rR (rS (lI (W ⊓ contK E N))) hU)
      (fun τ u => ((m τ).map (u + ·)).prod) := by
  refine ⟨hV.aut φ hφ, fun k hk => Subtype.ext (funext fun g => hT.1 k hk g), fun g => ?_,
    fun τ u => (hinf τ).2 u φ hφ⟩
  have hf : (fun k : Kinf E N => (cptRep E N k φ).1 g) ∈ lI (W ⊓ contK E N) := by
    refine mem_lI.2 fun k₀ => ⟨?_, ?_⟩
    · show (fun k => φ.1 (g * infGL E N (Unitary.toUnits (k₀ * k)))) ∈ W
      have := hT.2 (g * infGL E N (Unitary.toUnits k₀))
      simpa only [map_mul, mul_assoc] using this
    · show Continuous fun k => φ.1 (g * infGL E N (Unitary.toUnits (k₀ * k)))
      have := cont_K φ (g * infGL E N (Unitary.toUnits k₀))
      simpa only [map_mul, mul_assoc] using this
  have hfU := le_rS _ hf
  refine Submodule.subset_span ⟨(LinearMap.proj 1 : (Kinf E N → ℂ) →ₗ[ℂ] ℂ).comp
    (rS (lI (W ⊓ contK E N))).subtype, ⟨_, hfU⟩, funext fun k => ?_⟩
  change (cptRep E N k φ).1 g = (cptRep E N (1 * k) φ).1 g
  rw [one_mul]

end PositivityTheory.Rg.BcB.F.F5.Bo.FiniteIsomorphism

namespace PositivityTheory.Rg.BcB.F.F5.Bo

open PositivityTheory.Rg.BcB.SpectralAccumulation.AdmDiscPf FiniteIsomorphism

theorem FinIso_holds : FinIso := by
  intro E _ _ _ N K W m hK hW
  classical
  have : FiniteDimensional ℂ (W ⊓ contK E N : Submodule ℂ (Kinf E N → ℂ)) :=
    Submodule.finiteDimensional_of_le inf_le_left
  have : FiniteDimensional ℂ (rS (lI (W ⊓ contK E N))) := fd_rS_lI _
  have hU : ∀ u ∈ rS (lI (W ⊓ contK E N)), ∀ k, (fun x => u (x * k)) ∈ rS (lI (W ⊓ contK E N)) :=
    fun u hu k => rS_right hu k
  let F := Submodule.span ℂ (GlobalTheory.Published.AutFinGL.forms K (rR (rS (lI (W ⊓ contK E N))) hU)
    (fun τ u => ((m τ).map (u + ·)).prod))
  have : FiniteDimensional ℂ F := PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL E N K hK _
    (rR (rS (lI (W ⊓ contK E N))) hU) (isContRep_rR _ hU (cont_rS W)) _
  let P : Submodule ℂ (Sm E N) → Prop := fun V =>
    IsDiscrete V ∧ SpectralAccumulation.HasType K W V ∧ ∀ τ, HasInfCharGL V τ (m τ)
  let G : ℕ → Prop := fun l => ∃ V : Fin l → Submodule ℂ (Sm E N), (∀ i, P (V i)) ∧
    ∀ i j, i ≠ j → ¬ SpectralAccumulation.IsoV (V i) (V j)
  have hbound : ∀ l, G l → l ≤ Module.finrank ℂ F := by
    rintro l ⟨V, hVP, hVn⟩
    choose φ hφV hφ0 hφT using fun i => (hVP i).2.1
    have hmem : ∀ i, φ i ∈ F := fun i =>
      Submodule.subset_span (mem_forms_of hU (hVP i).1 (hVP i).2.2 (hφV i) (hφT i))
    have hli := linIndep V (fun i => (hVP i).1) hVn φ hφV hφ0
    have hli' : LinearIndependent ℂ (fun i => (⟨φ i, hmem i⟩ : F)) :=
      LinearIndependent.of_comp F.subtype hli
    simpa using hli'.fintype_card_le_finrank
  have h0 : G 0 := ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  have hl : G (Nat.findGreatest G (Module.finrank ℂ F)) := Nat.findGreatest_spec (Nat.zero_le _) h0
  obtain ⟨V, hVP, hVn⟩ := hl
  refine ⟨Finset.univ.image V, fun V' hV' => ?_, fun V' hd ht hi => ?_⟩
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hV'
    exact (hVP i).1
  · by_contra hno
    push Not at hno
    have hno' : ∀ i, ¬ SpectralAccumulation.IsoV V' (V i) := fun i => hno (V i) (Finset.mem_image_of_mem V (Finset.mem_univ i))
    have hG : G (Nat.findGreatest G (Module.finrank ℂ F) + 1) := by
      refine ⟨Fin.cons V' V, fun i => ?_, fun i j hij => ?_⟩
      · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
        · exact ⟨hd, ht, hi⟩
        · simpa only [Fin.cons_succ] using hVP i'
      · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩ <;>
          rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
        · exact absurd rfl hij
        · simpa only [Fin.cons_zero, Fin.cons_succ] using hno' j'
        · simp only [Fin.cons_zero, Fin.cons_succ]
          exact fun h => hno' i' (isoV_symm (hVP i').1.stable h)
        · simp only [Fin.cons_succ]
          exact hVn i' j' (fun h => hij (by rw [h]))
    have := Nat.le_findGreatest (hbound _ hG) hG
    omega

end PositivityTheory.Rg.BcB.F.F5.Bo

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.FinStrictHolds

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical



attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo.Tw.FiniteStrictOrder

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.FX.Bo

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem forall₂_ofFn {α β : Type*} (R : α → β → Prop) {c c' : ℕ} (h : c = c') (f : Fin c → α) (g : Fin c' → β)
    (H : ∀ i, R (f i) (g (Fin.cast h i))) : List.Forall₂ R (List.ofFn f) (List.ofFn g) := by
  subst h
  induction c with
  | zero => simp
  | succ c ih =>
    simp only [List.ofFn_succ]
    exact List.Forall₂.cons (by simpa using H 0) (ih _ _ fun i => by simpa using H i.succ)

theorem siso_trans {x y z : Σ M : ℕ, Submodule ℂ (Sm E M)} (hy : _root_.GlobalTheory.CuspRep.IsStable y.2) (hx : SIso x z) (hyz : SIso y z) :
    SIso x y := by
  obtain ⟨M, Vx⟩ := x
  obtain ⟨M', Vy⟩ := y
  obtain ⟨Mz, Vz⟩ := z
  obtain ⟨h1, h1'⟩ := hx
  obtain ⟨h2, h2'⟩ := hyz
  simp only at h1 h2
  subst h1
  subst h2
  exact ⟨rfl, PositivityTheory.Rg.BcB.F.F5.Bo.isoV_trans' h1' (PositivityTheory.Rg.BcB.F.F5.Bo.isoV_symm' hy h2')⟩

theorem c_le {a : ℕ} (P : Pre E a) : P.c ≤ a := by
  calc P.c = ∑ _i : Fin P.c, 1 := by simp
    _ ≤ ∑ i, P.N i := Finset.sum_le_sum fun i _ => P.pos i
    _ = a := P.h

theorem N_le {a : ℕ} (P : Pre E a) (j : Fin P.c) : P.N j ≤ a := by
  calc P.N j ≤ ∑ i, P.N i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    _ = a := P.h

theorem m_le {a : ℕ} (P : Pre E a) (m₀ : (E →+* ℂ) → Multiset ℂ) (hm : ∀ τ, ∑ j, P.m j τ = m₀ τ) (j : Fin P.c)
    (τ : E →+* ℂ) : P.m j τ ≤ m₀ τ := by
  rw [← hm τ]
  exact Finset.single_le_sum (f := fun j => P.m j τ) (fun _ _ => Multiset.zero_le _) (Finset.mem_univ j)

end PositivityTheory.Rg.BcB.F.FX.Bo.Tw.FiniteStrictOrder

namespace PositivityTheory.Rg.BcB.F.FX.Bo.Tw

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.FX.Bo FiniteStrictOrder

theorem FinStrict_holds : FinStrict := by
  intro E _ _ _ a Θ Ω hΘ hΩ m₀

  have hF := fun (M : ℕ) (K' : Subgroup (GL (Fin M) (Af E))) (W' : Submodule ℂ (Kinf E M → ℂ))
    (m' : (E →+* ℂ) → Multiset ℂ) (hK : IsOpen (K' : Set (GL (Fin M) (Af E)))) (hW : FiniteDimensional ℂ W') =>
    Bo.FinIso_holds E M K' W' m' hK hW
  choose V0 _hV0 hV0 using hF

  let Ms : Set ((E →+* ℂ) → Multiset ℂ) := Set.pi Set.univ fun τ => {s | s ≤ m₀ τ}
  have hMs : Ms.Finite := by
    refine Set.Finite.pi fun τ => ?_
    refine (Multiset.toFinset (Multiset.powerset (m₀ τ))).finite_toSet.subset fun s hs => ?_
    simpa [Multiset.mem_powerset] using hs

  let Reps : Set (Σ M : ℕ, Submodule ℂ (Sm E M)) :=
    ⋃ M ∈ Set.Iic a, ⋃ K' ∈ Θ M, ⋃ W' ∈ Ω M, ⋃ m' ∈ Ms,
      ⋃ (hK : IsOpen (K' : Set (GL (Fin M) (Af E)))), ⋃ (hW : FiniteDimensional ℂ W'),
        (Sigma.mk M) '' (V0 M K' W' m' hK hW : Set (Submodule ℂ (Sm E M)))
  have hReps : Reps.Finite :=
    (Set.finite_Iic a).biUnion fun M _ => (hΘ M).1.biUnion fun K' _ => (hΩ M).1.biUnion fun W' _ =>
      hMs.biUnion fun m' _ => Set.finite_iUnion fun hK => Set.finite_iUnion fun hW => (Finset.finite_toSet _).image _
  have := hReps.to_subtype
  have := hMs.to_subtype
  let Good : Pre E a → Prop := fun P =>
    (∀ j, ∃ K' ∈ Θ (P.N j), ∃ W' ∈ Ω (P.N j), HasType K' W' (P.V j)) ∧ (∀ τ, ∑ j, P.m j τ = m₀ τ)

  have hrep : ∀ P : Pre E a, Good P → ∀ j, ∃ z ∈ Reps, SIso ⟨P.N j, P.V j⟩ z := by
    intro P hP j
    obtain ⟨K', hK', W', hW', ht⟩ := hP.1 j
    have hKo := (hΘ _).2 K' hK'
    have hWf := (hΩ _).2 W' hW'
    obtain ⟨V', hV'm, hiso⟩ := hV0 _ K' W' (P.m j) hKo hWf (P.V j) (P.discrete j) ht (P.inf j)
    refine ⟨⟨P.N j, V'⟩, ?_, rfl, hiso⟩
    simp only [Reps, Set.mem_iUnion, Set.mem_image]
    exact ⟨P.N j, N_le P j, K', hK', W', hW', P.m j, fun τ _ => m_le P m₀ hP.2 j τ, hKo, hWf, V', hV'm, rfl⟩
  have hmem : ∀ P : Pre E a, Good P → ∀ j, P.m j ∈ Ms := fun P hP j τ _ => m_le P m₀ hP.2 j τ

  let part : Pre E a → ℕ → Option (Reps × Ms) := fun P i =>
    if h : i < P.c then
      (if h' : (∃ z ∈ Reps, SIso ⟨P.N ⟨i, h⟩, P.V ⟨i, h⟩⟩ z) ∧ P.m ⟨i, h⟩ ∈ Ms then
        some (⟨Classical.choose h'.1, (Classical.choose_spec h'.1).1⟩, ⟨P.m ⟨i, h⟩, h'.2⟩) else none)
    else none
  let key : Pre E a → Fin (a + 1) × (Fin a → Option (Reps × Ms)) := fun P =>
    (⟨min P.c a, Nat.lt_succ_of_le (min_le_right _ _)⟩, fun i => part P i.1)

  have hkey : ∀ P Q : Pre E a, Good P → Good Q → key P = key Q → Strict P Q := by
    intro P Q hP hQ hPQ
    have hc : P.c = Q.c := by
      have := congrArg (fun x => (x.1 : ℕ)) (congrArg Prod.fst hPQ)
      simpa [key, min_eq_left (c_le P), min_eq_left (c_le Q)] using this
    have hpart : ∀ j : Fin P.c, part P j.1 = part Q j.1 := fun j =>
      congrFun (congrArg Prod.snd hPQ) ⟨j.1, lt_of_lt_of_le j.2 (c_le P)⟩
    have hsome : ∀ (R : Pre E a) (hR : Good R) (j : Fin R.c), ∃ z : Reps, SIso ⟨R.N j, R.V j⟩ z.1 ∧
        part R j.1 = some (z, ⟨R.m j, hmem R hR j⟩) := by
      intro R hR j
      have h' : (∃ z ∈ Reps, SIso ⟨R.N ⟨j.1, j.2⟩, R.V ⟨j.1, j.2⟩⟩ z) ∧ R.m ⟨j.1, j.2⟩ ∈ Ms := ⟨hrep R hR j, hmem R hR j⟩
      refine ⟨⟨Classical.choose h'.1, (Classical.choose_spec h'.1).1⟩, (Classical.choose_spec h'.1).2, ?_⟩
      simp only [part, dif_pos j.2, dif_pos h']
    refine ⟨forall₂_ofFn SIso hc _ _ fun j => ?_, hc, fun j => ?_⟩
    · obtain ⟨z, hz, hPz⟩ := hsome P hP j
      obtain ⟨z', hz', hQz⟩ := hsome Q hQ (Fin.cast hc j)
      have e := (hpart j).trans (hQz : part Q j.1 = _)
      rw [hPz] at e
      simp only [Option.some.injEq, Prod.mk.injEq] at e
      rw [← e.1] at hz'
      exact siso_trans (Q.discrete _).stable hz hz'
    · obtain ⟨z, hz, hPz⟩ := hsome P hP j
      obtain ⟨z', hz', hQz⟩ := hsome Q hQ (Fin.cast hc j)
      have e := (hpart j).trans (hQz : part Q j.1 = _)
      rw [hPz] at e
      simp only [Option.some.injEq, Prod.mk.injEq, Subtype.mk.injEq] at e
      exact e.2

  let Im : Set (Fin (a + 1) × (Fin a → Option (Reps × Ms))) := key '' {P | Good P}
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin Im
  have hpre : ∀ i : Fin k, ∃ P, Good P ∧ key P = (e.symm i).1 := fun i => (e.symm i).2
  choose Pl hPl hkPl using hpre
  refine ⟨k, Pl, fun P h1 h2 => ?_⟩
  have hP : Good P := ⟨h1, h2⟩
  refine ⟨e ⟨key P, P, hP, rfl⟩, hkey P _ hP (hPl _) ?_⟩
  rw [hkPl, Equiv.symm_apply_apply]

end PositivityTheory.Rg.BcB.F.FX.Bo.Tw

end
end
end
