module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.PowNeOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FRGood
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ReadHalf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TreeParts
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLExistsLocalComponent
public import Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ExistsHasInfCharGL
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.LevIdem
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PPositions
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.BlockCandOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.EntryLeOfLg
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdjKer0
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ActHecke
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FrobeniusWeights.FrameMatrixPowerHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SlotEmbeddingsExistStatement
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.IwahoriPairLeMaximal
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.MconvZeroRight
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LocalActionPowers.Pfmone
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.ReadSplitOfJoin

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TreePrecursors.PreOfTreeHolds

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.PreOfTreePf

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem leafList_sum : ∀ {N : ℕ} (t : Tr E N), (t.leafList.map Sigma.fst).sum = N
  | _, .leaf V z => by simp [Tr.leafList]
  | _, .node t₁ t₂ => by
    simp only [Tr.leafList, List.map_append, List.sum_append, leafList_sum t₁, leafList_sum t₂]

theorem leafList_good : ∀ {N : ℕ} (t : Tr E N), t.Good → ∀ x ∈ t.leafList, x.1 = 0 ∨ IsDiscrete x.2
  | _, .leaf V z, h, x, hx => by
    simp only [Tr.leafList, List.mem_singleton] at hx
    subst hx
    simp only [Tr.Good] at h
    rcases h with ⟨h0, -, -⟩ | ⟨-, hd, -⟩
    · exact Or.inl h0
    · exact Or.inr hd
  | _, .node t₁ t₂, h, x, hx => by
    simp only [Tr.Good] at h
    simp only [Tr.leafList, List.mem_append] at hx
    rcases hx with hx | hx
    · exact leafList_good t₁ h.1 x hx
    · exact leafList_good t₂ h.2 x hx

theorem sum_filter_pos (l : List (Σ M : ℕ, Submodule ℂ (Sm E M))) :
    ((l.filter fun x => 0 < x.1).map Sigma.fst).sum = (l.map Sigma.fst).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases hx : 0 < x.1
    · simp [List.filter_cons, hx, ih]
    · have h0 : x.1 = 0 := by omega
      simp [List.filter_cons, hx, ih, h0]

theorem preOfTree : PreOfTree := by
  intro E _ _ _ N t ht _ _
  have hpos : ∀ x ∈ t.leafList.filter (fun x => 0 < x.1), 0 < x.1 ∧ IsDiscrete x.2 := by
    intro x hx
    rw [List.mem_filter] at hx
    have hp : 0 < x.1 := by simpa using hx.2
    rcases leafList_good t ht x hx.1 with h0 | hd
    · omega
    · exact ⟨hp, hd⟩
  obtain ⟨l, hl⟩ : ∃ l, l = t.leafList.filter (fun x => 0 < x.1) := ⟨_, rfl⟩
  rw [← hl] at hpos
  have hsum : (l.map Sigma.fst).sum = N := by rw [hl, sum_filter_pos, leafList_sum]
  have hg : ∀ i : Fin l.length, 0 < (l.get i).1 ∧ IsDiscrete (l.get i).2 :=
    fun i => hpos _ (List.get_mem l i)
  have hloc : ∀ (i : Fin l.length) (w : HeightOneSpectrum (𝓞 E)), ∃ σ, IsLocCompGL (l.get i).2 w σ :=
    fun i w => GlobalTheory.DiscLocEx.exists_isLocCompGL CuspFormAutomorphicBounds.automorphicFormsFiniteGL E _ _ (hg i).2 w
  choose σ hσ using hloc
  have hinf : ∀ (i : Fin l.length) (τ : E →+* ℂ), ∃ m, HasInfCharGL (l.get i).2 τ m :=
    fun i τ => PInfInd2A.exists_hasInfCharGL (hg i).2 τ
  choose m hm using hinf
  have hN : ∑ i : Fin l.length, (l.get i).1 = N := by
    have h1 : (List.ofFn fun i : Fin l.length => (l.get i).1) = l.map Sigma.fst := by
      apply List.ext_get <;> simp
    rw [← List.sum_ofFn, h1, hsum]
  refine ⟨⟨l.length, fun i => (l.get i).1, hN, fun i => (l.get i).2, σ, m, fun i => (hg i).1,
    fun i => (hg i).2, hσ, hm⟩, ?_⟩
  show (List.ofFn fun i : Fin l.length => (⟨(l.get i).1, (l.get i).2⟩ : Σ M : ℕ, Submodule ℂ (Sm E M))) =
    t.leafList.filter fun x => 0 < x.1
  rw [← hl]
  exact List.ofFn_get l

end PositivityTheory.Rg.BcB.SpectralAccumulation.PreOfTreePf

theorem PositivityTheory.Rg.BcB.SpectralAccumulation.preOfTree_holds : PositivityTheory.Rg.BcB.SpectralAccumulation.PreOfTree := PositivityTheory.Rg.BcB.SpectralAccumulation.PreOfTreePf.preOfTree

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.CharacterIntegrability.BetaPow

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.R3

attribute [local instance] borelG borelF borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem convF_zero {a b : ℕ} {A κ : Type} [Fintype κ] (ν : Measure (Hf E a b)) (ψ : Matrix κ κ (Hf E a b → ℂ)) :
    convF ν ψ (0 : A × κ → H E a b → ℂ) = 0 := by
  funext i x
  simp [convF]

theorem pw_succ_psi {B : Block E} (t : PT B) (j : ℕ) : (t.pw (j + 1)).ψ = mulF B.ν t.ψ (t.pw j).ψ := rfl

theorem sq_psi {B : Block E} (t : PT B) (k : ℕ) : (t.sq k).ψ = mulF B.ν (t.adj'.pw k).ψ (t.pw k).ψ := rfl

theorem convF_pw (hCM : Tail.ConvMul) {B : Block E} (t : PT B) {A : Type} (U : Subgroup (Hf E B.a B.b))
    (F : A × B.κ → H E B.a B.b → ℂ) (hU : IsOpen (U : Set (Hf E B.a B.b)))
    (hF : ∀ i, ∀ u ∈ U, ∀ x, F i (x * finH u) = F i x) :
    ∀ k, (∀ j ≤ k, IsFinM (t.pw j).ψ) → convF B.ν (t.pw k).ψ F = (convF B.ν t.ψ)^[k + 1] F := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hfin
    have h0 : IsFinM t.ψ := hfin 0 (Nat.zero_le _)
    have hk : IsFinM (t.pw k).ψ := hfin k (Nat.le_succ k)
    rw [pw_succ_psi, (hCM E B A t.ψ (t.pw k).ψ U F h0 hk hU hF).1, ih (fun j hj => hfin j (Nat.le_succ_of_le hj)),
      Function.iterate_succ_apply' (convF B.ν t.ψ) (k + 1)]

end PositivityTheory.Rg.BcB.F.R3

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.PPowNe

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical



namespace PositivityTheory.Rg.BcB.F.BC

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem pw_fin {E : Type} [Field E] [NumberField E] [IsCMField E] {B : Block E} (t : PT B) (h : IsFinM t.ψ) :
    ∀ j, IsFinM (t.pw j).ψ := by
  haveI : BorelSpace (Hf E B.a B.b) := ⟨rfl⟩
  haveI := B.hν
  intro j
  induction j with
  | zero => exact h
  | succ j ih => exact CG.PMul.mulF_fin B.ν h ih

theorem adj_fin {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {κ : Type} {ψ : Matrix κ κ (Hf E a b → ℂ)}
    (h : IsFinM ψ) : IsFinM (adjF ψ) := fun x y =>
  ⟨Complex.continuous_conj.comp ((h y x).1.comp continuous_inv),
    ((h y x).2.comp_homeomorph (Homeomorph.inv _)).comp_left (g := starRingEnd ℂ) (map_zero _)⟩

theorem powNeOf_holds : PowNeOf := by
  intro hCM E _ _ _ B t m A _ G ht hG hne h0
  choose U hU hF using hG
  have ho : IsOpen ((⨅ j, U j : Subgroup (Hf E B.a B.b)) : Set (Hf E B.a B.b)) := by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite hU
  have hf : ∀ i, ∀ u ∈ (⨅ j, U j : Subgroup (Hf E B.a B.b)), ∀ x, G i (x * finH u) = G i x :=
    fun i u hu => hF i u (Subgroup.mem_iInf.1 hu i)
  apply hne
  rw [R3.sq_psi, (hCM E B A _ _ _ G (pw_fin t.adj' (adj_fin ht) m) (pw_fin t ht m) ho hf).1,
    R3.convF_pw hCM t _ G ho hf m fun j _ => pw_fin t ht j, h0, R3.convF_zero]

end PositivityTheory.Rg.BcB.F.BC

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FrobeniusWeights.PLevRead

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig
open scoped Classical



namespace PositivityTheory.Rg.BcB.F.FG

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem levReadOf_holds : LevReadOf := by
  intro hLI E _ _ _ n S d a ha hS hd hPS
  refine ⟨⟨fun w => ⟨(Rd.LevOC.locLev_oc d hd a ha w).1, (Rd.LevOC.locLev_oc d hd a ha w).2.2⟩, ?_⟩,
    ⟨fun w => ⟨(Rd.LevOC.locLev₂_oc d hd a ha w).1, (Rd.LevOC.locLev₂_oc d hd a ha w).2.2⟩, ?_⟩, ?_⟩
  · filter_upwards [Rd.levCof d a] with w hw using hw.1
  · filter_upwards [Rd.levCof d a] with w hw using hw.2
  intro W₁ W₂ G hT
  obtain ⟨⟨h1o, -⟩, ⟨h2o, -⟩, hset, -⟩ := hLI E n S d a ha hS hd hPS
  have hTU : ∀ u ∈ (lev₁ S d a).prod (lev₂ S d a), ∀ x, G (x * finH u) = G x := fun u hu x =>
    hT.1 u.1 (Subgroup.mem_prod.1 hu).1 u.2 (Subgroup.mem_prod.1 hu).2 x
  obtain ⟨e, -, hcp, hcp', he₁, he₂⟩ := GlobalTheory.T.position_embeddings_exist (E := E) a (n - a) hS
  have hlev : ∀ (i : Slot S) m, m ∈ Rd.LevOC.C d a i → e i m ∈ (lev₁ S d a).prod (lev₂ S d a) := by
    intro i m hm
    have h : e i m ∈ Rd.LevOC.gSet S d a := by
      rw [Rd.LevOC.gSet_eq]
      intro j
      by_cases hij : i = j
      · subst hij
        rw [hcp]
        exact hm
      · rw [hcp' i j m hij]
        rcases j with w | w
        · exact (d.lev a w.1).one_mem
        · exact (d.lev₂ a w.1).one_mem
    have h' : e i m ∈ (((lev₁ S d a).prod (lev₂ S d a) : Subgroup (Hf E a (n - a))) : Set (Hf E a (n - a))) := by
      rw [hset]
      exact h
    exact h'
  refine ⟨⟨_, by rw [Subgroup.coe_prod]; exact h1o.prod h2o, hTU⟩, fun w hw => ⟨?_, fun hs => ?_⟩⟩
  · rintro ⟨m, hm⟩
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    funext x
    have h := hTU _ (hlev (.inl ⟨w, hw⟩) m hm) x
    rw [he₁] at h
    exact h
  · rintro ⟨m, hm⟩
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    funext x
    have h := hTU _ (hlev (.inr ⟨w, hw, hs⟩) m hm) x
    rw [he₂] at h
    exact h

end PositivityTheory.Rg.BcB.F.FG

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.BlockCandidatesOfInputs

section

@[expose] public section

namespace PositivityTheory.Rg.BcB.F.BC

theorem level_reading_holds : FG.LevRead := FG.levReadOf_holds (levIdem slots)

theorem block_candidates_of_inputs (h1 : ChiTr) (h2 : LimAt) (h3 : Ident) : BlockCand :=
  blockCand_of h1 h2 h3 (powNeOf_holds FA.convMul_holds) SpectralAccumulation.preOfTree_holds RS.joinEx_holds level_reading_holds
    (FG.frGood_of level_reading_holds) FG.frame_weight_holds

end PositivityTheory.Rg.BcB.F.BC
end
end
