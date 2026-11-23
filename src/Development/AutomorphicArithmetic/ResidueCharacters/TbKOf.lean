module

public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
public import Development.AutomorphicArithmetic.ResidueCharacters.TwistDef
public import Development.AutomorphicArithmetic.ResidueCharacters.InvariantsKilledOverCyclotomicAlt
public import Development.AutomorphicArithmetic.ResidueCharacters.LenLeTorsion
public import Development.AutomorphicArithmetic.ResidueCharacters.LocNum
public import Development.AutomorphicArithmetic.ResidueCharacters.LocRes
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Formalism.SharpRestriction.LevelLetterCocycles.JsetEmb
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionCorestrictionH1f
public import Formalism.WeaklyAdmissibleFiltrations.StatementTor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransferCocycleFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransferContinuousOfContinuousOn
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

-- Source module: Development.AutomorphicArithmetic.ResidueCharacters.TbTop

section

@[expose] public section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

namespace UpperTheory.N

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
theorem tb_top (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (h4 : LocalSituation.Conclusion4 D HW F) (hCo : CrysOnCond D HW F)
    (hW : ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
      EmbeddingTypeJumps.WachHypothesisLocal (LocalSituation.sit D.loc HW l (D.locA l) K s LL h) ((F l).E K s LL h).tie)
    (hF : ∀ K LL : FinExt l, TruncatedSeriesCountingIdentities.FontaineAt ((D.loc l).PD K) ↥LL.1 ↥(OL LL))
    (N h n t e g : ℕ) (K LL : FinExt l) (hg : Good K (sN l N) LL) (hKs : Ks K (sN l N) = K.1)
    (U : Finset ℤ) (hn : U.card ≤ n) (hb : ∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) (he : e < t) (ht : t ≤ h)
    (hgl : g ≤ Nat.log l N + 1)
    (Yt Ve : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hcrys : IsCrys ((D.loc l).PD K) Yt.ρ)
    (hjmp : ∀ τ, JumpsInV ((D.loc l).PD K) Yt.ρ τ (U : Set ℤ))
    (p : Yt.V →ₗ[↥LL.1] ↥LL.1) (hp : ∀ g v, p (Yt.ρ g v) = p v)
    (hint : ∀ v ∈ Yt.L.T, p v ∈ Set.range (algebraMap ↥(OL LL) ↥LL.1)) (e₀ : Yt.V) (he₀ : e₀ ∈ Yt.L.T) (hpe : p e₀ = 1)
    (h1 : Module.finrank ↥LL.1 Ve.V = 1)
    (hχ : ∀ g x, Ve.ρ g x = ((algebraMap ℚ_[l] ↥LL.1 (((D.loc l).PD K).χ g : ℚ_[l]))⁻¹) ^ e • x)
    (φ : Yt.V →ₗ[↥(OL LL)] (Ve.V ⧸ Ve.L.T))
    (hφ : ∀ g, ∀ y ∈ Yt.L.T, p y = 0 → φ (Yt.ρ g y) = actD Ve.L g (φ y)) :
    ∃ c : ℕ, c + g ≤ cBL l N h n t ∧
      ((l : ↥(OL LL)) ^ c) • (fun g => φ (Yt.ρ g e₀ - e₀)) ∈ HfD ((D.loc l).PD K) Ve.L := by
  haveI : IsDiscreteValuationRing ↥(OL LL) := Formalism.BasicNotions.Examples₂.LB.OL_dvr LL
  let Y := kerY Yt p e₀ hpe hp hint he₀
  have hcjY := cj_sub (hF K LL) (S := fun _ => (U : Set ℤ)) (GRep.ofLat Yt) (LinearMap.ker p)
    (ker_stable Yt p hp) ⟨hcrys, hjmp⟩
  have hsub : LocalSituation.Jset (LocalSituation.sit D.loc HW l (D.locA l) K _ LL hg) Y ⊆ U := fun a ha => by
    obtain ⟨τ, hτ⟩ := JsetEmb.jsetSplit_all D HW l K _ LL hg Y a ha
    exact hcjY.2 τ a hτ
  have hWY := hW K _ LL hg Y h h hcjY.1 fun a ha => hb a (hsub ha)
  have hCt := hCo l K _ LL hg Yt hcrys
  haveI : IsTopologicalRing (LocalSituation.sit D.loc HW l (D.locA l) K _ LL hg).LL := inferInstanceAs (IsTopologicalRing ↥LL.1)
  haveI : IsDomain (LocalSituation.sit D.loc HW l (D.locA l) K _ LL hg).O := inferInstanceAs (IsDomain ↥(OL LL))
  haveI : IsPrincipalIdealRing (LocalSituation.sit D.loc HW l (D.locA l) K _ LL hg).O :=
    inferInstanceAs (IsPrincipalIdealRing ↥(OL LL))
  have key := TBLoc.tb_part1 (LocalSituation.sit D.loc HW l (D.locA l) K _ LL hg) Yt p e₀ hpe hp hint he₀
    Subtype.val_injective _ (h4 l K _ LL hg).1 e h h _ Ve h1 hχ hCt hWY le_rfl φ hφ
  have e1 : LocalSituation.ell (LocalSituation.sit D.loc HW l (D.locA l) K _ LL hg) = l := (D.loc l).PD_p K
  refine ⟨LocalSituation.cTBY (LocalSituation.sit D.loc HW l (D.locA l) K _ LL hg) Y h h e, ?_, ?_⟩
  · have hvd := LocRes.vdeg_le K (s := sN l N) (m := LocalSituation.mN l (sN l N) (h + h))
      (le_max_left _ _) (by unfold LocalSituation.mN; omega)
    have e2 : (LocalSituation.sit D.loc HW l (D.locA l) K _ LL hg).W.s = sN l N := (HW l).W_s _ _ _ _
    have e3 : LocalSituation.gK (LocalSituation.sit D.loc HW l (D.locA l) K _ LL hg) = 0 := by
      unfold LocalSituation.gK
      rw [e2]
      show padicValNat _ (Module.finrank ℚ_[l] ↥(Ks K _)) - padicValNat _ (Module.finrank ℚ_[l] ↥K.1) = 0
      rw [hKs, Nat.sub_self]
    unfold LocalSituation.cTBY LocalSituation.vdegMs
    rw [e3, e1, e2]
    exact LocNum.cTB_le l N h n t e _ _ Fact.out U _ hsub hn hb he ht hvd hgl
  · have e4 : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) = (l : ↥(OL LL)) := by rw [(D.loc l).PD_p]
    rw [← e4]
    exact key

end UpperTheory.N

end
end
end

-- Source module: Development.AutomorphicArithmetic.ResidueCharacters.TransferMemBlochKatoCocycles

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations TensorProduct

noncomputable section

namespace UpperTheory.N.CorD

variable {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
    {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL]
    {K₀ K K₀' K' : Type} [Field K₀] [Field K] [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B] [Algebra K₀' BdR] [Algebra K' BdR]
    [IsScalarTower Qp K' BdR] [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]

open GlobalTheory.InducedSectionsSpanStatement

theorem transfer_mem_blochKato_cocycles [IsTopologicalGroup G'] (PD : PeriodData G Qp K₀ K B BdR) (PD' : PeriodData G' Qp K₀' K' B BdR)
    (ι : G →* G') (hι : Continuous ι) (he : Topology.IsEmbedding ι) (ho : IsOpen (ι.range : Set G'))
    [Fintype (G' ⧸ ι.range)] (hact : ∀ g b, PD.actB g b = PD'.actB (ι g) b) (T : LocLat G' Qp LL O)
    (z : G → T.V) (hz : z ∈ finiteCocycles PD (LiftingTheory.resLoc ι hι T).ρ) : trCochain ι T z ∈ finiteCocycles PD' T.ρ := by
  have hinj : Function.Injective ι := he.injective
  have hinv : ∀ a : G, Function.invFun ι (ι a) = a := fun a => Function.leftInverse_invFun hinj a
  have hmem := GlobalTheory.transfer_cocycle_formula LL G' T.V T.ρ ι.range
  obtain ⟨hzc, x, hx⟩ := hz
  obtain ⟨hzcont, hzcoc⟩ := hzc
  set f : G' → T.V := fun h => z (Function.invFun ι h) with hf
  have htr : ∀ g, trCochain ι T z g =
      ∑ q : G' ⧸ ι.range, T.ρ (Quotient.out (g • q)) (f ((Quotient.out (g • q))⁻¹ * g * Quotient.out q)) := by
    intro g
    rw [trCochain_apply]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · haveI : IsTopologicalAddGroup T.V :=
      { continuous_neg := by
          have := continuous_const_smul (-1 : LL) (T := T.V)
          simpa using this }
    have hρc : ∀ g : G', Continuous (T.ρ g) := fun g =>
      IsModuleTopology.continuous_of_linearMap (R := LL) (T.ρ g)
    have hfc : ContinuousOn f (ι.range : Set G') := by
      rw [continuousOn_iff_continuous_restrict]
      refine (hzcont.comp (he.toHomeomorph).symm.continuous).congr ?_
      rintro ⟨h, a, rfl⟩
      simp only [Function.comp_apply, hf, hinv]
      congr 1
    have hc := GlobalTheory.transfer_continuous_of_continuousOn LL G' T.V T.ρ ι.range ho hρc f hfc
    have hfun : (trCochain ι T z : G' → T.V) = fun g => ∑ q : G' ⧸ ι.range,
        T.ρ (Quotient.out (g • q)) (f ((Quotient.out (g • q))⁻¹ * g * Quotient.out q)) := funext htr
    rw [hfun]
    exact hc
  · intro a b
    rw [htr, htr, htr]
    refine hmem.2.1 f ?_ a b
    rintro _ ⟨a', rfl⟩ _ ⟨b', rfl⟩
    simp only [hf, ← map_mul, hinv]
    exact hzcoc a' b'
  · have hW := GlobalTheory.transfer_cocycle_formula LL G' (T.V ⊗[Qp] B) (repVB PD' T) ι.range
    refine ⟨∑ q : G' ⧸ ι.range, repVB PD' T (Quotient.out q) x, fun g => ?_⟩
    have key := hW.2.2.1 (fun h => f h ⊗ₜ[Qp] (1 : B)) x (by
      rintro _ ⟨a, rfl⟩
      simp only [hf, hinv]
      rw [hx a, actVB_res PD PD' ι hι hact T a x]
      rfl) g
    simp only at key
    rw [htr, TensorProduct.sum_tmul]
    have hstep : ∀ (h : G') (v : T.V), (T.ρ h v) ⊗ₜ[Qp] (1 : B) = repVB PD' T h (v ⊗ₜ[Qp] 1) := by
      intro h v
      exact (actVB_tmul_one PD' T h v).symm
    simp only [hstep]
    rw [key]
    rfl

theorem index_smul_mem [IsTopologicalGroup G'] (PD : PeriodData G Qp K₀ K B BdR) (PD' : PeriodData G' Qp K₀' K' B BdR)
    (ι : G →* G') (hι : Continuous ι) (he : Topology.IsEmbedding ι) (ho : IsOpen (ι.range : Set G'))
    [ι.range.FiniteIndex] (hact : ∀ g b, PD.actB g b = PD'.actB (ι g) b) (T : LocLat G' Qp LL O)
    (c : G' → T.V ⧸ T.L.T) (hc : ∀ a b, c (a * b) = c a + actD T.L a (c b))
    (hres : (fun g => c (ι g)) ∈ HfD PD (LiftingTheory.resLoc ι hι T).L) :
    ((ι.range.index : ℕ) : O) • c ∈ HfD PD' T.L := by
  haveI : Fintype (G' ⧸ ι.range) := Subgroup.fintypeQuotientOfFiniteIndex
  have hinj : Function.Injective ι := he.injective
  have hinv : ∀ a : G, Function.invFun ι (ι a) = a := fun a => Function.leftInverse_invFun hinj a
  obtain ⟨y, hy, bb, hbb, hsum⟩ := Submodule.mem_sup.mp hres
  obtain ⟨z, hz, rfl⟩ := hy
  obtain ⟨w, rfl⟩ := hbb
  have hzf : z ∈ finiteCocycles PD (LiftingTheory.resLoc ι hι T).ρ := hz
  have htrz := transfer_mem_blochKato_cocycles PD PD' ι hι he ho hact T z hzf
  have hD := GlobalTheory.transfer_cocycle_formula O G' (T.V ⧸ T.L.T) (repD T.L) ι.range
  set S' : T.V ⧸ T.L.T := ∑ q : G' ⧸ ι.range, c (Quotient.out q) with hS'
  set S : T.V ⧸ T.L.T := ∑ q : G' ⧸ ι.range, repD T.L (Quotient.out q) w with hS
  have hcsplit : ∀ a : G, c (ι a) = T.L.T.mkQ (z a) + (actD T.L (ι a) w - w) := by
    intro a
    have := congrFun hsum a
    rw [← this]
    rfl
  have h4 := hD.2.2.2 c (fun a b => hc a b)
  have h3 := hD.2.2.1 (fun h => actD T.L h w - w) w (fun h _ => rfl)
  have hkey : ∀ g : G', ((ι.range.index : ℕ) : O) • c g =
      T.L.T.mkQ (trCochain ι T z g) + (repD T.L g (S - S') - (S - S')) := by
    intro g
    have h4g := h4 g
    have h3g := h3 g
    dsimp only at h4g h3g
    have e1 : (∑ q : G' ⧸ ι.range, repD T.L (Quotient.out (g • q))
        (c ((Quotient.out (g • q))⁻¹ * g * Quotient.out q))) =
        T.L.T.mkQ (trCochain ι T z g) + ∑ q : G' ⧸ ι.range, repD T.L (Quotient.out (g • q))
          (actD T.L ((Quotient.out (g • q))⁻¹ * g * Quotient.out q) w - w) := by

      rw [trCochain_apply, map_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp (hD.1 g q)
      rw [← ha, hcsplit a, hinv, map_add (f := _)]
      rfl
    rw [Nat.cast_smul_eq_nsmul]
    have hh : ι.range.index • c g = (∑ q : G' ⧸ ι.range, repD T.L (Quotient.out (g • q))
        (c ((Quotient.out (g • q))⁻¹ * g * Quotient.out q))) - (repD T.L g S' - S') := by
      rw [h4g]
      abel
    rw [hh, e1, h3g, map_sub]
    abel
  refine Submodule.mem_sup.mpr ⟨T.L.T.mkQ.compLeft G' (trCochain ι T z), ⟨_, htrz, rfl⟩,
    fun g => repD T.L g (S - S') - (S - S'), ⟨S - S', rfl⟩, ?_⟩
  funext g
  rw [Pi.add_apply, Pi.smul_apply, hkey g]
  rfl

end UpperTheory.N.CorD

end
end
end

-- Source module: Development.AutomorphicArithmetic.ResidueCharacters.TbKOf

section

@[expose] public section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

namespace UpperTheory.N

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
theorem tbK_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (h4 : LocalSituation.Conclusion4 D HW F) (hCo : CrysOnCond D HW F)
    (hW : ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
      EmbeddingTypeJumps.WachHypothesisLocal (LocalSituation.sit D.loc HW l (D.locA l) K s LL h) ((F l).E K s LL h).tie)
    (hE : ∀ K LL : FinExt l, TwistK.TBe ((D.loc l).PD K) ↥LL.1 ↥(OL LL) (IK K))
    (hres : ElementDenominator.CrystallineRestrictionToExtension D.loc)
    (hF : ∀ K LL : FinExt l, TruncatedSeriesCountingIdentities.FontaineAt ((D.loc l).PD K) ↥LL.1 ↥(OL LL)) : TBK (D.loc l) := by
  intro N h n t K LL hC ht J U hn hb hJ
  refine ⟨?_, ?_⟩
  · intro Vy _ _ _ _ _ _ _ _ _ _ _ ρy Ly hcy hcrys hjmp p hp hint e₀ he₀ hpe e he Ve _ _ _ _ _ _ _ _ _ _ _ ρe Le hce hMat φ hφ
    obtain ⟨K', hKK, hg, hKs, hnor, hidx⟩ := LocNum.exists_up hC
    have hle : GK K' ≤ GK K := GK_le hKK
    have hε := TBLoc.eps_lat ((D.loc l).PD K) (O := ↥(OL LL)) Le.T e hMat
    let Yt : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) := { V := Vy, ρ := ρy, cont := hcy, L := Ly }
    let VeL : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) := { V := Ve, ρ := ρe, cont := hce, L := Le }
    obtain ⟨r1, j1⟩ := LocRes.res_crys D.loc hres hF hKK hle Yt hcrys
    have hχ : ∀ (g : ↥(GK K')) x, (LocRes.res hle VeL).ρ g x =
        ((algebraMap ℚ_[l] ↥LL.1 (((D.loc l).PD K').χ g : ℚ_[l]))⁻¹) ^ e • x := fun g x => by
      rw [(D.loc l).PD_χ]
      have := hε.2 (Subgroup.inclusion hle g) x
      rw [(D.loc l).PD_χ] at this
      exact this
    obtain ⟨c, hcle, key⟩ := tb_top D HW F l h4 hCo hW hF N h n t e _ K' LL hg hKs U hn hb he ht hidx
      (LocRes.res hle Yt) (LocRes.res hle VeL) r1 (fun τ a ha => hJ _ (hjmp _ a ((j1 τ a).1 ha))) p
      (fun g v => hp _ v) hint e₀ he₀ hpe hε.1 hχ φ (fun g y hy hy0 => hφ _ y hy hy0)
    haveI := K.2
    haveI := K'.2
    have hix := GlobalTheory.InducedSectionsSpanStatement.inclusion_GK_index K' K hle
    have hpos : 0 < Module.finrank ℚ_[l] ↥K'.1 := Module.finrank_pos
    have hpos' : 0 < Module.finrank ℚ_[l] ↥K.1 := Module.finrank_pos
    have hgi : Module.finrank ℚ_[l] ↥K'.1 / Module.finrank ℚ_[l] ↥K.1 = (Subgroup.inclusion hle).range.index := by
      rw [← hix, Nat.mul_div_cancel _ hpos']
    have hi0 : (Subgroup.inclusion hle).range.index ≠ 0 := fun h => by rw [h, zero_mul] at hix; omega
    haveI : (Subgroup.inclusion hle).range.FiniteIndex := ⟨hi0⟩
    have hcoc : ∀ a b, φ (ρy (a * b) e₀ - e₀) = φ (ρy a e₀ - e₀) + actD Le a (φ (ρy b e₀ - e₀)) := fun a b => by
      rw [← hφ a _ (Ly.T.sub_mem (Ly.stable b e₀ he₀) he₀) (by rw [map_sub, hp, sub_self]), ← map_add (f := _), map_sub, map_mul]
      congr 1
      simp
    have hcor := CorD.index_smul_mem ((D.loc l).PD K') ((D.loc l).PD K) (Subgroup.inclusion hle)
      (continuous_subtype_val.subtype_mk _) (Topology.IsEmbedding.inclusion hle)
      (by rw [Subgroup.inclusion_range]
          exact (IntermediateField.fixingSubgroup_isOpen K'.1).preimage continuous_subtype_val)
      (fun g b => by rw [(D.loc l).PD_actB, (D.loc l).PD_actB]; rfl) VeL
      (((l : ↥(OL LL)) ^ c) • fun g => φ (ρy g e₀ - e₀))
      (fun a b => by
        show ((l : ↥(OL LL)) ^ c) • φ (ρy (a * b) e₀ - e₀) =
          ((l : ↥(OL LL)) ^ c) • φ (ρy a e₀ - e₀) + actD Le a (((l : ↥(OL LL)) ^ c) • φ (ρy b e₀ - e₀))
        rw [hcoc, smul_add, map_smul])
      key
    have hfin := LocRes.pow_val_smul_mem LL _ hi0 hcor
    rw [hgi] at hcle
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hcle
    rw [(D.loc l).PD_p, hd, pow_add, mul_comm, mul_smul, pow_add, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ hfin
  · intro e he Ve _ _ _ _ _ _ _ _ _ _ _ ρe Le hce hMat
    have hε := TBLoc.eps_lat ((D.loc l).PD K) (O := ↥(OL LL)) Le.T e hMat
    let VeL : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) := { V := Ve, ρ := ρe, cont := hce, L := Le }
    have hT := hE K LL e VeL hε.1 hε.2
    exact TBLoc.tbe_clauses ((D.loc l).PD K) Le _ _ rfl e _ hT.2.1 hT.2.2 (hT.1 _)

end UpperTheory.N

end
end
end
