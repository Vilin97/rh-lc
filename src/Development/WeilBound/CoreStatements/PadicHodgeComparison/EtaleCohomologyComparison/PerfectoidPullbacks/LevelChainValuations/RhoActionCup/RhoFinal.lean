module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.FinDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.CupZnApply
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.HomGalGoodRHof
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.HomLevGood
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.HomPullGoodRHof
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.InstSt
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.RhoFirstChernLaw
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationFunctorialStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationUniqueStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationUnitClassStatement
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.CoefficientReductionFirstChernClassTateTwist
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.CupGood
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.RHof
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CrSEqOne
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.CoefficientReductionFirstChernClassTateTwist
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.NmHONmPullBBMap
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
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.ReductionChangeLevel
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.RhoActionCup.CupGenA
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.RhoActionCup.RhoFirstChernFormula

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.HomGalGood

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section



open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section
variable {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) (g : K.fixingSubgroup) (M : Model l K)

namespace GaloisEquivariantMaps


open LevelPullbackIdentities in
def etaGal (s : ℕ) (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T)) :
    (nmS (nmGB hL g M) 1 s).o.G ⋙ (smB M s hL hQ).o.G ⟶ (smB M s hL hQ).o.G ⋙ (nmS (nmGA hL g M) l s).o.G where
  app T := ObjectProperty.homMk (mkH (RingHom.id T.obj.B) (fun r => congrArg T.obj.i (hL.σ_ι g r).symm)
    (DPMorphism.id T.obj.δ).isDPMorphism (fun _ h => h)
    (Subtype.ext (Prod.ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun a =>
      (qid _ (fun _ h => h) _).trans (congrArg (fun b => T.obj.y.1.1 (Ideal.Quotient.mk _ b)) (hL.σ_ι g a).symm)))
      ((spec_qid _ (fun _ h => h) _).trans (by
        show ((T.obj.y.1.2 ≫ 𝟙 M.gen) ≫ pullback.fst _ _ : _ ⟶ M.X) = (T.obj.y.1.2 ≫ pullback.fst _ _) ≫ 𝟙 M.X
        simp)))))
  naturality _ _ f := ObjectProperty.hom_ext _ (CrystallineSemistableComparison.Pb.hom_ext rfl)

end GaloisEquivariantMaps

theorem nmHO_nmGB_bMap (s : ℕ) (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T)) (j : ℕ) (z : HO (QA L M s) j) :
    nmHO (nmGB hL g M) 1 s j (bMap M s hL hQ j z) = bMap M s hL hQ j (nmHO (nmGA hL g M) l s j z) := by
  have i1 : RingHomCompTriple L.ι (L.σB g) ((L.σB g).comp L.ι) := ⟨rfl⟩
  have i2 : RingHomCompTriple (L.σA g) L.ι ((L.σB g).comp L.ι) := ⟨RingHom.ext fun a => hL.σ_ι g a⟩
  have e₁ := CrystallineSemistableComparison.pull_pull ((L.σB g).comp L.ι) (smB M s hL hQ).o (nmS (nmGB hL g M) 1 s).o j z
  have e₂ := CrystallineSemistableComparison.pull_pull ((L.σB g).comp L.ι) (nmS (nmGA hL g M) l s).o (smB M s hL hQ).o j z
  exact e₁.trans ((CrystallineSemistableComparison.P.prism ((smB M s hL hQ).o.comp (σ'' := (L.σB g).comp L.ι) (nmS (nmGB hL g M) 1 s).o)
    ((nmS (nmGA hL g M) l s).o.comp (σ'' := (L.σB g).comp L.ι) (smB M s hL hQ).o)
    (GaloisEquivariantMaps.etaGal hL g M s hQ) (fun T x => rfl) j z).trans e₂.symm)

variable (s : ℕ) (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T))
  (rH : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s) none ((l : L.A) ^ n) j)

theorem homGal_good_of_galRed (hr : GalRed hL g M s rH) : (homGal hL g M s hQ rH).Good :=
  { ℓ := rfl
    lam := hL.σ_lam g
    ι := fun a => (hL.σ_ι g a).symm
    o := hL.σB_K g
    tS := fun n j x => ((M.galH false j (IntermediateField.fixingSubgroupEquiv K g)).comm n x).symm
    r := hr
    red := fun n j z => nmHM_redM _ l s none n j z
    b := nmHO_nmGB_bMap hL g M s hQ
    μ := fun j v => (nm_muB (nmGB hL g M) (Category.id_comp _) 1 s (hL.σB_K g) j v).trans
      (congrArg _ (pullR_id' M.q j v)) }

end

section
variable {m : ℕ} {L : Lev (per l K) m}
  (d : ∀ n, RedIn (B.DD false (PAlg.base l) n) (B.κb (okToOC l K) false n) L.γ l n)
  (hc : ∀ n (c : Acris l), (d n).ρ ((PAlg.base l).cris n c) = Ideal.Quotient.mk _ (L.lam c))

theorem galRed_rHof (hL : L.Good) (g : K.fixingSubgroup) (M : Model l K) (s : ℕ) : GalRed hL g M s (rHof d hc M s) := by
  intro n j x
  exact (red_nm (d n) (d n) s (nmGA hL g M) _ _ _ _ _ (hc n) (hc n) _ _ (fun _ _ => (Category.comp_id _).symm)
    (by
      intro y
      obtain ⟨c, rfl⟩ := ((RL.base_acr (PAlg.base l) PAlg.isBase_base).2 n).1 y
      rw [PAlg.galBase_cris, hc, hc]
      exact (congrArg (Ideal.Quotient.mk _) (hL.σ_lam g c)).symm) none j x).symm

end

end CrystallineSemistableComparison.Pb.Kap
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.HomPullRHofGood

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section



open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section
variable {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (s : ℕ)
  (hQN : ∀ T, QB L N s T → QA L N s (((nmB N hL).mor 0).obj T))
  (hQM : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T))
  (rHN : ∀ n j, N.Hc false n j →ₛₗ[L.lam] HM (QA L N s) none ((l : L.A) ^ n) j)
  (rHM : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s) none ((l : L.A) ^ n) j)

theorem homPull_good_of_nmHM_pull
    (hr : ∀ n j x, nmHM (nmPullA L u hu) l s none n j (rHN n j x) =
      rHM n j (B.pullHc (okToOC l K) (B.schMap u hu) false n j x)) :
    (homPull hL u hu s hQN hQM rHN rHM).Good :=
  { ℓ := rfl
    lam := fun _ => rfl
    ι := fun _ => rfl
    o := fun _ => rfl
    tS := fun n j x => ((Model.pullH u hu false j).comm n x).symm
    r := hr
    red := fun n j z => nmHM_redM _ l s none n j z
    b := nmHO_nmPullB_bMap hL u hu s hQN hQM
    μ := nm_muB (nmPullB L u hu) (Model.genMap_q u hu) 1 s (fun _ => rfl) }

end

theorem homPull_rHof_good {m : ℕ} {L : Lev (per l K) m}
    (d : ∀ n, RedIn (B.DD false (PAlg.base l) n) (B.κb (okToOC l K) false n) L.γ l n)
    (hc : ∀ n (c : Acris l), (d n).ρ ((PAlg.base l).cris n c) = Ideal.Quotient.mk _ (L.lam c))
    {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (s : ℕ) (hL : L.Good)
    (hQN : ∀ T, QB L N s T → QA L N s (((nmB N hL).mor 0).obj T))
    (hQM : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T)) :
    (homPull hL u hu s hQN hQM (rHof d hc N s) (rHof d hc M s)).Good :=
  homPull_good_of_nmHM_pull hL u hu s hQN hQM _ _ (rHof_pull d hc u hu s)

end CrystallineSemistableComparison.Pb.Kap
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.RHofLev

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section



open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

variable (S : LevSys (per l K)) (hS : S.Good) (hC : ∀ m, (S.L m).CrisOK)

namespace LevelIdentityMorphisms

def idMor (M : Model l K) (n : ℕ) :
    GlobalTheory.LogCris.Mor (B.Lc (B.schFn M.p) (okToOC l K) false n) (B.Lc (B.schFn M.p) (okToOC l K) false n) (RingHom.id _) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l false n) (b' := B.bs l false n) (ht := rfl) (ht' := rfl)
    (RingHom.id _) rfl (DPMorphism.id _).isDPMorphism (𝟙 _) (fun _ _ _ => rfl)

abbrev idOm (M : Model l K) (n : ℕ) :
    CH.Mor (B.Oc (B.schFn M.p) (okToOC l K) false n) (B.Oc (B.schFn M.p) (okToOC l K) false n) (RingHom.id (Acris l)) :=
  B.omMor (idMor M n) (RingHom.id (Acris l)) (fun _ => rfl)

def idEta (M : Model l K) (n : ℕ) : (CH.Mor.id (B.Oc (B.schFn M.p) (okToOC l K) false n)).G ⟶ (idOm M n).G where
  app T := LevelPullbackIdentities.thHom ⟨fun j => Empty.elim j⟩ rfl (RingHom.id T.B) (fun r => rfl) (DPMorphism.id T.δ).isDPMorphism
    (fun _ h => h)
    (Subtype.ext (Prod.ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun a => LevelPullbackIdentities.qid _ (fun _ h => h) _))
      (LevelPullbackIdentities.spec_qid _ (fun _ h => h) _)))
  naturality _ _ f := Thick.Hom.ext (RingHom.ext fun _ => rfl) (funext fun j => Empty.elim j)

theorem idMor_pull (M : Model l K) (n j : ℕ) (x : M.Hc false n j) : (idOm M n).pull j x = x := by
  have h1 : (CH.Mor.id (B.Oc (B.schFn M.p) (okToOC l K) false n)).pull j x = x :=
    (CrystallineSemistableComparison.P.pull_comp (CH.Mor.id _) (CH.Mor.id _) j x).2
  have h2 := CrystallineSemistableComparison.P.prism (CH.Mor.id (B.Oc (B.schFn M.p) (okToOC l K) false n)) (idOm M n) (idEta M n)
    (fun T x => rfl) j x
  exact h2.symm.trans h1

end LevelIdentityMorphisms

theorem nmHM_nmLevA_rHof_succ (M : Model l K) (m s n j : ℕ) (x : M.Hc false n j) :
    nmHM (nmLevA S hS m M) l s none n j (rHof (dOf S hS hC (m + 1)) (hcOf S hS hC (m + 1)) M s n j x) =
      rHof (dOf S hS hC m) (hcOf S hS hC m) M s n j x := by
  have hρ : ∀ y, (dOf S hS hC m n).ρ (RingHom.id _ y) = lnMap (S.dA m) l le_rfl ((dOf S hS hC (m + 1) n).ρ y) := by
    intro y
    obtain ⟨c, rfl⟩ := ((RL.base_acr (PAlg.base l) PAlg.isBase_base).2 n).1 y
    rw [RingHom.id_apply, hcOf, hcOf]
    exact congrArg (Ideal.Quotient.mk _) (hS.dlam m c).symm
  have e := red_nm (dOf S hS hC (m + 1) n) (dOf S hS hC m n) s (nmLevA S hS m M) (LevelIdentityMorphisms.idMor M n)
    ((PAlg.base l).cris n) ((PAlg.base l).cris n) (S.L (m + 1)).lam (S.L m).lam
    (hcOf S hS hC (m + 1) n) (hcOf S hS hC m n) (RingHom.id _) (fun _ => rfl) (fun _ _ => (Category.comp_id _).symm)
    hρ none j x
  exact (congrArg _ (LevelIdentityMorphisms.idMor_pull M n j x).symm).trans e |>.symm

end CrystallineSemistableComparison.Pb.Kap
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.RhoActionCup.RhoFinal

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section



open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap.Mo

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
variable (S : LevSys (per l K)) (hS : S.Good) (hC : ∀ m, (S.L m).CrisOK)

variable [FiniteDimensional ℚ_[l] K]

theorem lev_good (M : Model l K) (m s : ℕ) : (homLev S hS m M s (qb_le (hS.lev (m + 1)) M s) (qb_le (hS.lev m) M s)
    (rHof (dOf S hS hC (m + 1)) (hcOf S hS hC (m + 1)) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s)).Good := by
  exact
    { ℓ := rfl
      lam c := hS.dlam m c
      ι a := hS.dι m a
      o k := hS.dK m k
      tS n j x := rfl
      r n j x := nmHM_nmLevA_rHof_succ S hS hC M m s n j x
      red n j z := nmHM_redM _ l s none n j z
      b j z := nmHO_nmLevB_bMap S hS m M s _ _ j z
      μ j v := (nm_muB (nmLevB S hS m M) (Category.id_comp _) 1 s (hS.dK m) j v).trans (congrArg _ (pullR_id' M.q j v)) }

theorem rho_lev_pf : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ j m x f,
    rhoK S hS hC a j (m + 1) x f → rhoK S hS hC a j m x ((S.dB m).toAddMonoidHom.comp f) := by
  intro M a hM j m x f ⟨hM', s₀, hs₀⟩
  refine ⟨hM', ?_⟩
  obtain ⟨s₁, hs₁⟩ := chK_good S hS hC M hM (m + 1)
  obtain ⟨s₂, hs₂⟩ := chK_good S hS hC M hM m
  refine ⟨max s₀ (max s₁ s₂), fun s hs => ?_⟩
  have h := GlobalTheory.T.realization_functorial (chK S hS hC M (m + 1) s) (chK S hS hC M m s)
    (homLev S hS m M s (qb_le (hS.lev (m + 1)) M s) (qb_le (hS.lev m) M s)
      (rHof (dOf S hS hC (m + 1)) (hcOf S hS hC (m + 1)) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s))
    (hs₁ s (by omega)) (hs₂ s (by omega)) (lev_good S hS hC M m s)
    (show (M.HS false j).lim from x).1 f (hs₀ s (by omega))
  exact h

theorem rho_act_of (hG : ∀ (M : Model l K) m s g, (homGal (hS.lev m) g M s (qb_le (hS.lev m) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s)).Good) : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ j m (g : K.fixingSubgroup) x f,
    rhoK S hS hC a j m x f → rhoK S hS hC a j m (((dat Amp).H a).act j g x) (((S.L m).σB g).toAddMonoidHom.comp f) := by
  intro M a hM j m g x f ⟨hM', s₀, hs₀⟩
  obtain ⟨s₁, hs₁⟩ := chK_good S hS hC M hM m
  refine ⟨hM', max s₀ s₁, fun s hs => ?_⟩
  exact GlobalTheory.T.realization_functorial (chK S hS hC M m s) (chK S hS hC M m s) (homGal (hS.lev m) g M s (qb_le (hS.lev m) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s))
    (hs₁ s (by omega)) (hs₁ s (by omega)) (hG M m s g) (show (M.HS false j).lim from x).1 f (hs₀ s (by omega))

theorem rho_nat_of (hP : ∀ (M N : Model l K) (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) m s,
    (homPull (hS.lev m) u hu s (qb_le (hS.lev m) N s) (qb_le (hS.lev m) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) N s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s)).Good) : ∀ {M N : Model l K} {u : M.X ⟶ N.X} {hu : u ≫ N.p = M.p} {a : (dat Amp).Ch M} {b : (dat Amp).Ch N}
    (μ : (dat Amp).Mo u hu a b), M.Sm → N.Sm → ∀ j m x f f', rhoK S hS hC b j m x f → rhoK S hS hC a j m ((dat Amp).pullH μ j x) f' →
      ∀ φ, f' φ = f (φ ∘ₗ pullR j (Model.genMap u hu) (Model.genMap_q u hu)) := by
  intro M N u hu a b μ hM hN j m x f f' ⟨_, s₀, h₀⟩ ⟨_, s₀', h₀'⟩ φ
  obtain ⟨s₁, hs₁⟩ := chK_good S hS hC M hM m
  obtain ⟨s₂, hs₂⟩ := chK_good S hS hC N hN m
  obtain ⟨s, e0, e1, e2, e3⟩ : ∃ s, s₀ ≤ s ∧ s₀' ≤ s ∧ s₁ ≤ s ∧ s₂ ≤ s := ⟨s₀ + s₀' + s₁ + s₂, by omega⟩
  have h := GlobalTheory.T.realization_functorial (chK S hS hC N m s) (chK S hS hC M m s) _ (hs₂ s e3) (hs₁ s e2) (hP M N u hu m s)
    (show (N.HS false j).lim from x).1 f (h₀ s e0)
  have e := GlobalTheory.T.realization_unique (chK S hS hC M m s) (hs₁ s e2) _ f' _ (h₀' s e1) h
  rw [e]
  rfl

theorem rho_one_of (hU : ∀ (M : Model l K) m s, (cupOf (hS.lev m) M s (qb_le (hS.lev m) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s)).Good) : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ m x f, rhoK S hS hC a 0 m x f → ((dat Amp).H a).one x →
    ∀ φ, f φ = algebraMap K (S.L m).B (φ (oneK M.q)) := by
  intro M a hM m x f ⟨_, s₀, h₀⟩ hx φ
  obtain ⟨s₁, hs₁⟩ := chK_good S hS hC M hM m
  obtain ⟨s, e0, e1⟩ : ∃ s, s₀ ≤ s ∧ s₁ ≤ s := ⟨s₀ + s₁, by omega⟩
  have h := h₀ s e0
  rw [show (show (M.HS false 0).lim from x).1 = (cupOf (hS.lev m) M s (qb_le (hS.lev m) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s)).oneS from
    funext ((one_iff (hS.lev m) M s (qb_le (hS.lev m) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s) a x).1 hx)] at h
  exact GlobalTheory.T.realization_unit_class (chK S hS hC M m s) (hs₁ s e1) _ (hU M m s) f h φ

theorem rho_cup_pf : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ {i j : ℕ} m x y z f g h,
    rhoK S hS hC a i m x f → rhoK S hS hC a j m y g → rhoK S hS hC a (i + j) m z h → ((dat Amp).H a).cup x y z →
    ∀ {e e' : ℕ} (b : Module.Basis (Fin e) K (HdR M.q i)) (b' : Module.Basis (Fin e') K (HdR M.q j))
      (φ : Module.Dual K (HdR M.q (i + j))),
      h φ = ∑ s, ∑ s', f (b.coord s) * g (b'.coord s') * algebraMap K (S.L m).B (φ (cupK M.q rfl (b s) (b' s'))) := by
  intro M a hM i j m x y z f g h hx hy hz hc e e' b b' φ
  refine hx.2.elim fun s₀ h₀ => hy.2.elim fun s₁ h₁ => hz.2.elim fun s₂ h₂ => (chK_good S hS hC M hM m).elim fun s₃ h₃ => ?_
  exact cup_genA (hS.lev m) M (s₀ + s₁ + s₂ + s₃) _ _ (h₃ _ (by omega)) (cupOf_rHof_good _ M _ _ _ _) _ _ _ f g h (h₀ _ (by omega))
    (h₁ _ (by omega)) (h₂ _ (by omega))
    ((cup_iff_cS_lim (hS.lev m) M 0 (qb_le (hS.lev m) M 0) (rHof (dOf S hS hC m) (hcOf S hS hC m) M 0) a x y z).1 hc) b b' φ

include hS hC in
theorem rhoSys_ex : Nonempty (RhoSys S Model.Sm (dat Amp) fun a c => IsFirstChernDeRham _ (lineK a.1) c) :=
  ⟨{ ρ := rhoK S hS hC
     ex := rho_ex_pf S hS hC
     uniq := rho_uniq_pf S hS hC
     add := rho_add_pf S hS hC
     smul := rho_smul_pf S hS hC
     lin' := rho_lin'_pf S hS hC
     lev := rho_lev_pf S hS hC
     act := rho_act_of S hS hC fun M m s g => by
       have hL := hS.lev m
       have hRed := galRed_rHof (dOf S hS hC m) (hcOf S hS hC m) hL g M s
       exact
         { ℓ := rfl
           lam c := hL.σ_lam g c
           ι a := (hL.σ_ι g a).symm
           o k := hL.σB_K g k
           tS n j x := ((M.galH false j (IntermediateField.fixingSubgroupEquiv K g)).comm n x).symm
           r n j x := hRed n j x
           red n j z := nmHM_redM _ l s none n j z
           b j z := nmHO_nmGB_bMap hL g M s _ j z
           μ j v := (nm_muB (nmGB hL g M) (Category.id_comp _) 1 s (hL.σB_K g) j v).trans
             (congrArg _ (pullR_id' M.q j v)) }
     nat := rho_nat_of S hS hC fun M N u hu m s => homPull_rHof_good _ _ u hu s _ _ _
     fil := rho_fil_pf S hS hC
     cup := rho_cup_pf S hS hC
     one := rho_one_of S hS hC fun M m s => cupOf_rHof_good _ M s _ _ _
     c1 := rho_firstChern_formula S hS hC }⟩

end CrystallineSemistableComparison.Pb.Kap.Mo
end
end
end
