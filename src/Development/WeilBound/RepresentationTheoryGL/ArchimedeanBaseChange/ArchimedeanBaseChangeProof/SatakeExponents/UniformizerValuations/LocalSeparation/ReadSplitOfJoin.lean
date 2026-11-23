module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistDiscreteCsd
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFlipGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasInfCharGLRankZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HintZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterThetaInvariantExponent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueWeightDefiniteUnitaryAt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeSpehOfDiscreteSeries
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitAtOfValuation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSubquotSmIndCongr
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivOfSameSatakeParameters
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasSatakeOfIsSatVecGL
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.UnramB
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatVMapMulChi
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmVecTranslate
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.LeafSeparation.LeafModHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.PPairSat
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.PReadModOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.PTreeModOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeVecMemFixed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.SaturationTransportPair

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChiDetPowSplitCentre

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS
open GlobalTheory.BCT.TwistDisc
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.JoinDatum

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

structure Part (E : Type) [Field E] [NumberField E] [IsCMField E] where
  M : ℕ
  V : Submodule ℂ (Sm E M)
  σ : ∀ w : HeightOneSpectrum (𝓞 E), SmIrr (GL (Fin M) (w.adicCompletion E))
  m : (E →+* ℂ) → Multiset ℂ
  pos : 0 < M
  discrete : IsDiscrete V
  loc : ∀ w, IsLocCompGL V w (σ w)
  inf : ∀ τ, HasInfCharGL V τ (m τ)

def partOf {n : ℕ} (P : Pre E n) (i : Fin P.c) : Part E :=
  ⟨P.N i, P.V i, P.σ i, P.m i, P.pos i, P.discrete i, P.loc i, P.inf i⟩

def Part.twist (x : Part E) (χ : HChar E) (hu : χ.IsUnitary)
    (hs : ∀ (a : ℕ) (t : ℝ), chiDet a χ (splitCentre E a t) = 1) : Part E :=
  ⟨x.M, x.V.map (mulChi x.M χ).toLinearMap,
    fun w => (x.σ w).twist (CuspSub.locDet x.M χ w) (CuspSub.isOpen_ker_locDet χ w),
    fun τ => (x.m τ).map (· + expo χ τ), x.pos, isDiscrete_map hu (hs x.M) x.discrete,
    fun w => isLocCompGL_map χ (x.loc w), fun τ => hasInfCharGL_map (x.inf τ) χ⟩

def ofParts {n c : ℕ} (p : Fin c → Part E) (h : ∑ i, (p i).M = n) : Pre E n :=
  ⟨c, fun i => (p i).M, h, fun i => (p i).V, fun i => (p i).σ, fun i => (p i).m, fun i => (p i).pos,
    fun i => (p i).discrete, fun i => (p i).loc, fun i => (p i).inf⟩

theorem isUnitary_pow {μ : HChar E} {e : InfinitePlace E → ℤ} (hμ : IsMu μ e) (k : ℕ) : (μ ^ k).IsUnitary := fun x => by
  rw [pow_val_apply, Units.val_pow_eq_pow_val, norm_pow, hμ.1 x, one_pow]

theorem chiDet_pow_splitCentre {μ : HChar E} {e : InfinitePlace E → ℤ} (hμ : IsMu μ e) (k a : ℕ) (t : ℝ) :
    chiDet a (μ ^ k) (splitCentre E a t) = 1 := by
  show chiDet a μ _ ^ k = 1
  rw [chiDet_splitCentre hμ.2.2.2.2, one_pow]

theorem joinEx : JoinEx := by
  intro E _ _ _ n a b μ e Pa Pb hμ hn
  let p : Fin Pa.c → Part E := fun i =>
    (partOf Pa i).twist (μ ^ b) (isUnitary_pow hμ b) (chiDet_pow_splitCentre hμ b)
  let q : Fin Pb.c → Part E := fun i =>
    (partOf Pb i).twist (μ ^ a) (isUnitary_pow hμ a) (chiDet_pow_splitCentre hμ a)
  have hsum : ∑ i, (Fin.append p q i).M = n := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [← hn]
    exact congrArg₂ (· + ·) Pa.h Pb.h
  refine ⟨ofParts (Fin.append p q) hsum, ?_⟩
  have h1 : parts (ofParts (Fin.append p q) hsum) =
      List.map (fun x : Part E => (⟨x.M, x.V⟩ : Σ M : ℕ, Submodule ℂ (Sm E M))) (List.ofFn (Fin.append p q)) := by
    rw [List.map_ofFn]
    rfl
  rw [IsJoin, h1, List.ofFn_fin_append, List.map_append, parts, parts, List.map_ofFn, List.map_ofFn, List.map_ofFn, List.map_ofFn]
  rfl

end GlobalTheory.CompanionTheory.JoinDatum

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsBisFurther

section

@[expose] public section

open scoped Classical

open NumberField GlobalTheory.CuspRep Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.SpectralAccumulation

noncomputable section

namespace GlobalTheory.CompanionTheory.WeightJoin

theorem main : PositivityTheory.Rg.BcB.F.RS.WeightJoin := by
  intro E _ _ _ hU n a b μ e π lam n₁ n₂ hn hμ hπ hw h₁ h₂ hinf τ lam' hτ
  obtain ⟨-, he, hc⟩ := GlobalTheory.BCT.MuProps.main E hU μ e hμ
  let U : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
  rw [GlobalTheory.BCT.TwistDisc.expo_pow, GlobalTheory.BCT.TwistDisc.expo_pow]
  rcases NumberField.InfinitePlace.embedding_mk_eq τ with h | h
  · have hv := hw (InfinitePlace.mk τ)
    have hinfv := hinf (InfinitePlace.mk τ)
    have hev := he (InfinitePlace.mk τ)
    rw [h] at hv hinfv hev
    rw [GlobalTheory.DefU.hasWeightAt_unique U τ hτ hv, hev, ← hinfv]
    congr 1 <;> exact Multiset.map_congr rfl fun x _ => by ring
  · have hv := GlobalTheory.DefiniteBC.hasWeightAt_conjugate hn (hw (InfinitePlace.mk τ))
    have hinfv := hinf (InfinitePlace.mk τ)
    have hev := hc (InfinitePlace.mk τ)
    have hs₁ := (h₁ (InfinitePlace.mk τ).embedding).2
    have hs₂ := (h₂ (InfinitePlace.mk τ).embedding).2
    have hcc : ComplexEmbedding.conjugate (InfinitePlace.mk τ).embedding = τ := by
      rw [h]; exact star_star τ
    have hcc' : (starRingEnd ℂ).comp (InfinitePlace.mk τ).embedding = τ := hcc
    rw [hcc'] at hs₁ hs₂
    rw [hcc] at hv hev
    rw [GlobalTheory.DefU.hasWeightAt_unique U τ hτ hv, GlobalTheory.DefiniteBC.infOfWeight_dual, ← hinfv, hev, hs₁, hs₂,
      Multiset.map_add, Multiset.map_map, Multiset.map_map, Multiset.map_map, Multiset.map_map]
    congr 1 <;> exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp_apply]; ring

end GlobalTheory.CompanionTheory.WeightJoin

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfOfTwPart

section

@[expose] public section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.JoinInfProof

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def infOf (τ : E →+* ℂ) (x : Σ M : ℕ, Submodule ℂ (Sm E M)) : Multiset ℂ :=
  if h : ∃ m, HasInfCharGL x.2 τ m then h.choose else 0

theorem infOf_eq {τ : E →+* ℂ} {x : Σ M : ℕ, Submodule ℂ (Sm E M)} (h0 : x.2 ≠ ⊥) {m : Multiset ℂ}
    (h : HasInfCharGL x.2 τ m) : infOf τ x = m := by
  have hex : ∃ m, HasInfCharGL x.2 τ m := ⟨m, h⟩
  unfold infOf
  rw [dite_eq_left hex]
  exact GlobalTheory.BcSpehProof.hasInfCharGL_unique h0 hex.choose_spec h

theorem sum_m {n : ℕ} (P : Pre E n) (τ : E →+* ℂ) : ∑ i, P.m i τ = ((parts P).map (infOf τ)).sum := by
  rw [PositivityTheory.Rg.BcB.F.RS.parts, List.map_ofFn, List.sum_ofFn]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (infOf_eq (P.discrete i).ne_bot (P.inf i τ)).symm

theorem infOf_twPart {n : ℕ} (P : Pre E n) (χ : HChar E) (τ : E →+* ℂ) (i : Fin P.c) :
    infOf τ (twPart χ ⟨P.N i, P.V i⟩) = (P.m i τ).map (· + expo χ τ) := by
  have hne : Submodule.map ((GlobalTheory.CuspRep.mulChi (P.N i) χ : Sm E (P.N i) ≃ₗ[ℂ] Sm E (P.N i)) :
      Sm E (P.N i) →ₗ[ℂ] Sm E (P.N i)) (P.V i) ≠ ⊥ := by
    intro hb
    exact (P.discrete i).ne_bot (Submodule.map_eq_bot_iff.1 hb)
  exact infOf_eq hne (GlobalTheory.BCT.TwistDisc.hasInfCharGL_map (P.inf i τ) χ)

theorem sum_tw {n : ℕ} (P : Pre E n) (χ : HChar E) (τ : E →+* ℂ) :
    (((parts P).map (twPart χ)).map (infOf τ)).sum = (∑ i, P.m i τ).map (· + expo χ τ) := by
  rw [PositivityTheory.Rg.BcB.F.RS.parts, List.map_ofFn, List.map_ofFn, List.sum_ofFn]
  have hmap : ∀ s : Finset (Fin P.c), (∑ i ∈ s, P.m i τ).map (· + expo χ τ) =
      ∑ i ∈ s, (P.m i τ).map (· + expo χ τ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Multiset.map_add (f := _), ih]
  rw [hmap Finset.univ]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact infOf_twPart P χ τ i

end GlobalTheory.CompanionTheory.JoinInfProof

theorem GlobalTheory.CompanionTheory.JoinInfProof.joinInf : PositivityTheory.Rg.BcB.F.RS.JoinInf := by
  intro E _ _ _ n a b χ₁ χ₂ Pa Pb D hJ τ
  rw [sum_m D τ, hJ, List.map_append, List.sum_append, sum_tw Pa χ₁ τ, sum_tw Pb χ₂ τ]

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatSplit

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SatSplitAt

theorem satSplit : PositivityTheory.Rg.BcB.F.RS.SatSplit := by
  rintro E _ _ _ n π D w B ⟨σ, hc, hs⟩ ⟨b, hb, rfl⟩
  obtain ⟨P, hsub, -, hsat⟩ := GlobalTheory.PfBCI.unram_component D.h w (D.σ · w) b hb
  obtain ⟨α, hα, hσ⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ σ.ρ _).1
    (GlobalTheory.LFun.SatCompare.hasSatakeGL_iff.2 ⟨⟨σ.smooth, σ.irred⟩, hs⟩)
  obtain ⟨y, hy⟩ := hsat.exists_vec
  have hP : GlobalTheory.SmGL.HasSatake P.ρ α :=
    GlobalTheory.CompanionTheory.SatComp.hasSatake_of_isSatVecGL ⟨P.smooth, P.irred⟩ α (hα ▸ hy)
  obtain ⟨e⟩ := GlobalTheory.SmGL.SphUniq.equiv_of_parInd _ _ hP.1 hσ.1 hP.2.2 hσ.2.2 hP.2.1 hσ.2.1
  exact ⟨σ, (GlobalTheory.SmGL.IsSubquotient.of_surjective e.toIntertwiningMap e.toLinearEquiv.surjective).trans hsub, hc⟩

end GlobalTheory.CompanionTheory.SatSplitAt

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.PTreeSatOf

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.RS

theorem tso_map_heckeVec {G V X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
    {ρ : Representation ℂ G V} {τ : Representation ℂ G X} {K : Subgroup G} {h : G → ℂ} (hK : IsCommensurated K)
    (hh : h ∈ Hecke ℂ K) (L : V →ₗ[ℂ] X) {x : V} (hL : ∀ g, L (ρ g x) = τ g (L x)) :
    L (heckeVec ρ K h x) = heckeVec τ K h (L x) := by
  refine (L.toAddMonoidHom.map_finsum (finite_heckeVec hK hh ρ x)).trans (finsum_congr fun c => ?_)
  simp [hL]

theorem tso_heckeVec_mem {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {K : Subgroup G} {h : G → ℂ} (S : Submodule ℂ V) (hS : ∀ g, ∀ y ∈ S, ρ g y ∈ S) {x : V} (hx : x ∈ S) :
    heckeVec ρ K h x ∈ S := by
  unfold heckeVec
  exact finsum_induction (· ∈ S) S.zero_mem (fun _ _ => S.add_mem) fun c => S.smul_mem _ (hS _ _ hx)

theorem tso_heckeVec_zero {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {K : Subgroup G} {h : G → ℂ} : heckeVec ρ K h 0 = 0 := by
  simp [heckeVec]

theorem treeSatOf_holds : TreeSatOf := by
  intro hT E _ _ _ N t P w hg hu htp ⟨φ0, hφ0S, hφ00, hφ0K⟩
  obtain ⟨hinv, J, L, heq, hsep⟩ := hT E N t P w hg hu htp
  have hKo := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w N).1
  have hKc := Final.GLintComm E w N
  have fixK : ∀ φ, (∀ k ∈ KGL w (n := N), finRep E N (locGL E N w k) φ = φ) →
      φ ∈ fixed ((finRep E N).comp (locGL E N w)) (KGL w (n := N)) :=
    fun φ h => GlobalTheory.LGrp.mem_fixed.2 fun k hk => h k hk
  have smK : ∀ φ, φ ∈ fixed ((finRep E N).comp (locGL E N w)) (KGL w (n := N)) → SmVec ((finRep E N).comp (locGL E N w)) φ :=
    fun φ h => ⟨_, hKo, h⟩
  have hLfix : ∀ j φ, φ ∈ t.space → φ ∈ fixed ((finRep E N).comp (locGL E N w)) (KGL w (n := N)) →
      L j φ ∈ fixed (lp P w) (KGL w (n := N)) := fun j φ hS hf =>
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => by rw [← heq j k φ hS (smK _ hf), GlobalTheory.LGrp.mem_fixed.1 hf k hk]
  obtain ⟨j, hj⟩ : ∃ j, L j φ0 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hφ00 (hsep φ0 hφ0S (smK _ (fixK _ hφ0K)) hc)
  obtain ⟨b, hb, -⟩ := GlobalTheory.SatInd.exists_sat_multiProd P.h (π := fun i => (P.σ i w).ρ) (fun i => (P.σ i w).smooth)
    (fun i => (P.σ i w).irred) (hLfix j φ0 hφ0S (fixK _ hφ0K)) hj
  have hvec : ∀ f ∈ fixed (lp P w) (KGL w (n := N)), f ≠ 0 → IsSatVecGL w (lp P w) f (∑ i, b i) := fun f hf hf0 => by
    obtain ⟨S, hS, hfS⟩ := GlobalTheory.SatInd.exists_sat_multiProd P.h (π := fun i => (P.σ i w).ρ)
      (fun i => (P.σ i w).smooth) (fun i => (P.σ i w).irred) hf hf0
    have e : S = b := funext fun a => (hS a).unique (hb a)
    rw [← e]
    exact hfS
  have hcard : (∑ i, b i).card = N := (hvec _ (hLfix j φ0 hφ0S (fixK _ hφ0K)) hj).2.2.1
  refine ⟨_, ⟨b, fun i => ⟨(hb i).1, hb i⟩, rfl⟩, fun φ hφS hφ0 hφK => ?_⟩
  have hf := fixK _ hφK
  refine ⟨hφ0, hf, hcard, fun ϖ hϖ i hi => ?_⟩
  have hh := GlobalTheory.LFun.Tj_mem_hecke (n := N) hϖ i
  have hTS := tso_heckeVec_mem (K := KGL w (n := N)) (h := Tj ℂ N (Ov E w) ϖ i) t.space hinv hφS
  have hTf := GlobalTheory.LFun.SatCompare.heckeVec_mem_fixed hKc hh hf
  refine sub_eq_zero.1 (hsep _ (t.space.sub_mem hTS (t.space.smul_mem _ hφS))
    (smK _ (sub_mem hTf (Submodule.smul_mem _ _ hf))) fun j' => ?_)
  have key := tso_map_heckeVec (τ := lp P w) hKc hh (L j') fun g => heq j' g φ hφS (smK _ hf)
  rw [LinearMap.map_sub, LinearMap.map_smul]
  refine sub_eq_zero.2 (key.trans ?_)
  by_cases h0 : L j' φ = 0
  · exact (congrArg (heckeVec (lp P w) (KGL w (n := N)) (Tj ℂ N (Ov E w) ϖ i)) h0).trans
      (tso_heckeVec_zero.trans ((smul_zero _).symm.trans (congrArg _ h0.symm)))
  · exact (hvec _ (hLfix j' φ hφS hf) h0).2.2.2 ϖ hϖ i hi

end PositivityTheory.Rg.BcB.F.RS

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.ReadSplitOfJoin

section

@[expose] public section

namespace PositivityTheory.Rg.BcB.F.RS

theorem joinEx_holds : JoinEx := GlobalTheory.CompanionTheory.JoinDatum.joinEx

theorem joinInf_holds : JoinInf := GlobalTheory.CompanionTheory.JoinInfProof.joinInf

theorem joinSat_holds : JoinSat := GlobalTheory.CompanionTheory.JoinSatPf.joinSat

theorem treeInf_holds : TreeInf := GlobalTheory.CompanionTheory.TreeInfSum.treeInf

theorem weightJoin_holds : WeightJoin := GlobalTheory.CompanionTheory.WeightJoin.main

theorem muLoc_holds' : MuLoc := GlobalTheory.CompanionTheory.MuLocal.muLoc_holds

theorem treeMod_of (h : JoinMod) : TreeMod := treeModOf_holds leafMod_holds GlobalTheory.CompanionTheory.NodeSep.nodeMod h

theorem readMod_of (h : JoinMod) : ReadMod := readModOf_holds (treeMod_of h)

theorem readSplit_of_join (h : JoinMod) : ReadSplit :=
  readSplit_of (treeSatOf_holds (treeMod_of h)) pairSat_holds thetaSat2_holds GlobalTheory.CompanionTheory.CtS.ctSat muLoc_holds' joinSat_holds
    GlobalTheory.CompanionTheory.SatSplitAt.satSplit GlobalTheory.CompanionTheory.ConjSat.satConj

end PositivityTheory.Rg.BcB.F.RS
end
end
