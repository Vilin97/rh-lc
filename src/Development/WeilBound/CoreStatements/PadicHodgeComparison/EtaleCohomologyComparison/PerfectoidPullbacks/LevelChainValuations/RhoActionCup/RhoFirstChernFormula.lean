module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.RhoFirstChernLaw
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRealizationOfCompatibleStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationAddStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationFunctorialStatement
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.OneSTr
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationUniqueStatement
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.HomSGood
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.RhoActionCup.RHofTrGen
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtSide
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.IsProperOfProj
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.CrystallineFirstChernLevelCompat
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.InstSt
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.RHof
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LieComplementChartContDiffAt
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.RSubOneMem
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.CoefficientReductionFirstChernClassTateTwist
import Mathlib.Tactic.Linter.Style
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.HomLevGood
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.fil_lev

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationSmul

section

@[expose] public section

open CrystallineSemistableComparison.Pb.Kap

namespace GlobalTheory.CompanionTheory.KapChain

theorem rho_smul : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) {j : ℕ}
    (c : Λ) (x : ∀ n, C.S n j) (f : Module.Dual K (C.V j) →+ B), C.Rho x f →
    C.Rho (c • x) ((AddMonoidHom.mulLeft (C.ι (C.lam c))).comp f) := by
  intro Λ A B K _ _ _ _ C j c x f hf
  obtain ⟨h1, e, z, h2, h3⟩ := hf
  refine ⟨?_, e, C.lam c • z, ?_, ?_⟩
  · intro k φ
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, h1]
    ring
  · intro n
    rw [map_smul, h2 n, Pi.smul_apply, LinearMap.map_smulₛₗ, smul_comm]
  · intro m bs
    rw [LinearMap.map_smulₛₗ, ← h3 bs]
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, mul_smul]
    rw [← Finset.smul_sum, smul_comm]

end GlobalTheory.CompanionTheory.KapChain
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationSmulStatement

section

@[expose] public section

open CrystallineSemistableComparison.Pb.Kap

theorem _root_.GlobalTheory.T.realization_smul : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) {j : ℕ} (c : Λ) (x : ∀ n, C.S n j) (f : Module.Dual K (C.V j) →+ B), C.Rho x f → C.Rho (c • x) ((AddMonoidHom.mulLeft (C.ι (C.lam c))).comp f) := by
  first | exact @GlobalTheory.CompanionTheory.KapChain.rho_smul | exact GlobalTheory.CompanionTheory.KapChain.rho_smul | (intros; apply GlobalTheory.CompanionTheory.KapChain.rho_smul <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.CovSm

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section



open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem cov_sm_pf (M : Model l K) (hM : M.Sm) : Nonempty (Cov M.q) := by
  have := sm_proper_q hM
  exact (cov_ex M.q).1 (sm_smooth_q hM)

end CrystallineSemistableComparison.Pb.Kap
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.CrystallineFirstChernLevelCompat

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section



open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {m : ℕ} {L : Lev (per l K) m} (hL : L.Good)
  (d : ∀ n, RedIn (B.DD false (PAlg.base l) n) (B.κb (okToOC l K) false n) L.γ l n)
  (hc : ∀ n (c : Acris l), (d n).ρ ((PAlg.base l).cris n c) = Ideal.Quotient.mk _ (L.lam c)) (M : Model l K) (s : ℕ)

theorem crystalline_firstChern_level [FiniteDimensional ℚ_[l] K] (hM : M.Sm) (U : Cov M.q) (hU : ∀ α, U.d α + m ≤ s) (hs : m ≤ s)
    (a : (dat Amp).Ch M) (x : ((dat Amp).H a).N 2) (hx : (dat Amp).c1H a x) (c : HdR M.q 2) (hcK : IsFirstChernDeRham M.q (lineK a.1) c) :
    (chainOf hL M s (qb_le hL M s) (rHof d hc M s)).Rho (fun n => (show (M.HS false 2).lim from x).1 n) (evB M c) := by
  obtain ⟨N, i, -, -, hi⟩ := a.2
  have hcov := sSup_𝒱D a.1 N i hi
  obtain ⟨z, hz, -⟩ := thickening_firstChern_existsUnique L.γ M.p l s a.1 hcov
  refine ⟨fun k φ => ?_, 0, z, fun n => ?_, fun {e} bs => ?_⟩
  · show algebraMap K L.B (k • φ c) = algebraMap K L.B k * algebraMap K L.B (φ c)
    rw [smul_eq_mul, map_mul]
  · rw [pow_zero, one_smul]
    exact coefficientReduction_firstChernClass_tateTwist (d n) M.p s ((PAlg.base l).cris n) L.lam (hc n) a.1 hcov _ z (hx n) hz
  · rw [pow_zero, one_smul]
    have h1 : bMap M s hL (qb_le hL M s) 2 z = muB L.γB M.q 1 s {⊤} 2 c :=
      thickening_firstChern_pullback (nmB M hL) (QA L M s) (TF 1 s) (Or.inl ⟨rfl, 1, s, rfl⟩) (qb_le hL M s) a.1 s z _ hcov hz
        (deRham_firstChern_to_thickening L.γB M.q s (lineK a.1) c hcK)
    refine Eq.trans ?_ h1.symm
    show ∑ t, algebraMap K L.B (bs.coord t c) • muB L.γB M.q 1 s {⊤} 2 (bs t) = muB L.γB M.q 1 s {⊤} 2 c
    conv_rhs => rw [← bs.sum_repr c]

    rw [map_sum]
    exact Finset.sum_congr rfl fun t _ => (LinearMap.map_smulₛₗ _ _ _).symm

end CrystallineSemistableComparison.Pb.Kap
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.RHofIncl

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section



open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

theorem red_s_pf : ∀ {O A R Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [CommRing Λ] {I : Ideal A} {γ : DividedPowers I}
    {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ} (d : RedIn δ κ γ l n) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (s s' : ℕ) (𝒱 : Set X.Opens) (h : TS γ q l s 𝒱 ≤ TS γ q l s' 𝒱) (c : Λ →+* R) (lam : Λ →+* A)
    (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a)) (r : Option ℤ) (j : ℕ) (x : CH.H (B.OM (nlFun δ l X q κ) c) j),
    ((incl h).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) (incl_std h r ((l : A) ^ n))).pull j
      ((redMor q s' d 𝒱 c lam hc r).pull j x) = (redMor q s d 𝒱 c lam hc r).pull j x := by
  intro O A R Λ _ _ _ _ _ I γ J δ κ l n d X q s s' 𝒱 h c lam hc r j x
  rw [← (CrystallineSemistableComparison.P.pull_comp (σ'' := lam) (redMor q s' d 𝒱 c lam hc r) ((incl h).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) (incl_std h r ((l : A) ^ n))) j x).1]
  refine CrystallineSemistableComparison.P.prism ((redMor q s' d 𝒱 c lam hc r).comp (σ'' := lam) ((incl h).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) (incl_std h r ((l : A) ^ n)))) (redMor q s d 𝒱 c lam hc r) (𝟙 (redG q s d 𝒱)) (fun T y => ?_) j x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  rfl

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
variable (S : LevSys (per l K)) (hS : S.Good) (hC : ∀ m, (S.L m).CrisOK)

theorem rHof_incl_pf (M : Model l K) (m : ℕ) {s s' : ℕ} (h : s ≤ s') (n j : ℕ) (x : M.Hc false n j) :
    inclHM M h n j (rHof (dOf S hS hC m) (hcOf S hS hC m) M s' n j x) = rHof (dOf S hS hC m) (hcOf S hS hC m) M s n j x :=
  red_s_pf _ M.p s s' {⊤} (ts_le _ M.p l h {⊤}) _ _ _ none j x

end CrystallineSemistableComparison.Pb.Kap
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.RhoActionCup.RhoFirstChernFormula

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section



open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap.Mo

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
variable (S : LevSys (per l K)) (hS : S.Good) (hC : ∀ m, (S.L m).CrisOK)

variable [FiniteDimensional ℚ_[l] K]

theorem chK_good (M : Model l K) (hM : M.Sm) (m : ℕ) :
    ∃ s₁, ∀ s, s₁ ≤ s → (chK S hS hC M m s).Good := by
  obtain ⟨U⟩ := cov_sm_pf M hM
  refine ⟨Finset.univ.sup U.d + (m + 1), fun s hs => ?_⟩
  refine chain_good (hS.lev m) M s hM U (fun α => ?_) (by omega) _ (rHof_tr_gen _ _ M s)
  have := Finset.le_sup (f := U.d) (Finset.mem_univ α)
  omega

theorem rho_mono (M : Model l K) (m : ℕ) {s s' : ℕ} (h : s ≤ s') (hG : (chK S hS hC M m s).Good)
    (hG' : (chK S hS hC M m s').Good) {j : ℕ} (x : ∀ n, M.Hc false n j) (f : Module.Dual K (HdR M.q j) →+ (S.L m).B)
    (hf : (chK S hS hC M m s').Rho x f) : (chK S hS hC M m s).Rho x f := by
  have H := GlobalTheory.T.realization_functorial (chK S hS hC M m s') (chK S hS hC M m s)
    (homS (hS.lev m) M h (qb_le (hS.lev m) M s) (qb_le (hS.lev m) M s')
      (rHof (dOf S hS hC m) (hcOf S hS hC m) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s'))
    hG' hG (homS_good_of_inclHM _ _ _ _ _ _ _ (rHof_incl_pf S hS hC M m h)) x f hf
  have e : (homS (hS.lev m) M h (qb_le (hS.lev m) M s) (qb_le (hS.lev m) M s')
      (rHof (dOf S hS hC m) (hcOf S hS hC m) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s')).tr j f = f := by
    ext φ
    rfl
  rw [e] at H
  exact H

theorem rho_uniq_pf : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ j m x f f',
    rhoK S hS hC a j m x f → rhoK S hS hC a j m x f' → f = f' := by
  intro M a hM j m x f f' ⟨_, s₀, h⟩ ⟨_, s₀', h'⟩
  obtain ⟨s₁, hg⟩ := chK_good S hS hC M hM m
  exact GlobalTheory.T.realization_unique (chK S hS hC M m (max s₁ (max s₀ s₀'))) (hg _ (le_max_left _ _)) _ f f'
    (h _ (le_trans (le_max_left _ _) (le_max_right _ _))) (h' _ (le_trans (le_max_right _ _) (le_max_right _ _)))

theorem rho_ex_pf : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ j m x, ∃ f, rhoK S hS hC a j m x f := by
  intro M a hM j m x
  obtain ⟨s₁, hg⟩ := chK_good S hS hC M hM m
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_realization_of_compatible (chK S hS hC M m s₁) (hg s₁ le_rfl) (show (M.HS false j).lim from x).1
    (fun n => (show (M.HS false j).lim from x).2 n)
  refine ⟨f, hM, s₁, fun s hs => ?_⟩
  obtain ⟨g, hgs⟩ := GlobalTheory.T.exists_realization_of_compatible (chK S hS hC M m s) (hg s hs) (show (M.HS false j).lim from x).1
    (fun n => (show (M.HS false j).lim from x).2 n)
  have e : g = f := GlobalTheory.T.realization_unique _ (hg s₁ le_rfl) _ g f (rho_mono S hS hC M m hs (hg s₁ le_rfl) (hg s hs) _ g hgs) hf
  rwa [e] at hgs

theorem rho_add_pf : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ j m x y f g,
    rhoK S hS hC a j m x f → rhoK S hS hC a j m y g → rhoK S hS hC a j m (x + y) (f + g) := by
  intro M a hM j m x y f g ⟨_, s₀, h⟩ ⟨_, s₀', h'⟩
  exact ⟨hM, max s₀ s₀', fun s hs => GlobalTheory.T.realization_add (chK S hS hC M m s) _ _ f g
    (h s (le_trans (le_max_left _ _) hs)) (h' s (le_trans (le_max_right _ _) hs))⟩

theorem rho_smul_pf : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ j m (c : (per l K).A) x f, rhoK S hS hC a j m x f →
    rhoK S hS hC a j m (c • x) ((AddMonoidHom.mulLeft ((S.L m).ι ((S.L m).lam c))).comp f) := by
  intro M a hM j m c x f ⟨_, s₀, h⟩
  exact ⟨hM, s₀, fun s hs => GlobalTheory.T.realization_smul (chK S hS hC M m s) c _ f (h s hs)⟩

theorem rho_lin'_pf : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ j m x f, rhoK S hS hC a j m x f →
    ∀ (k : K) φ, f (k • φ) = algebraMap K (S.L m).B k * f φ := by
  intro M a hM j m x f ⟨_, s₀, h⟩ k φ
  exact (h s₀ le_rfl).1 k φ

theorem rho_fil_pf : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ j m x f, rhoK S hS hC a j m x f → ∀ n r : ℕ, n ≤ m →
    (dat Amp).fil a j n x → ∀ φ : Module.Dual K (HdR M.q j), (∀ h ∈ FilR M.q j (r + 1), φ h = 0) →
      f φ ∈ pdP (S.L m).γB (n - r) := by
  intro M a hM j m x f ⟨_, s₀, h⟩ n r hnm hfil φ hφ
  obtain ⟨U⟩ := cov_sm_pf M hM
  have hU : ∀ α, U.d α + (m + 1) ≤ max s₀ (Finset.univ.sup U.d + (m + 1)) := fun α => by
    have := Finset.le_sup (f := U.d) (Finset.mem_univ α)
    omega
  exact fil_lev_pf (hS.lev m) (dOf S hS hC m) (hcOf S hS hC m) M _ hM U hU (by omega) _
    (fun n => (show (M.HS false j).lim from x).2 n) f (h _ (le_max_left _ _)) n r (by omega) hfil φ hφ

theorem rho_firstChern_formula : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ m x f c, rhoK S hS hC a 2 m x f → (dat Amp).c1H a x →
    IsFirstChernDeRham _ (lineK a.1) c → ∀ φ, f φ = algebraMap K (S.L m).B (φ c) := by
  intro M a hM m x f c ⟨_, s₀, h⟩ hx hc φ
  obtain ⟨U⟩ := cov_sm_pf M hM
  obtain ⟨s₁, hg⟩ := chK_good S hS hC M hM m
  have hU : ∀ α, U.d α + (m + 1) ≤ max (max s₀ s₁) (Finset.univ.sup U.d + (m + 1)) := fun α => by
    have := Finset.le_sup (f := U.d) (Finset.mem_univ α)
    omega
  have H := crystalline_firstChern_level (hS.lev m) (dOf S hS hC m) (hcOf S hS hC m) M _ hM U hU (by omega) a x hx c hc
  have e := GlobalTheory.T.realization_unique (chK S hS hC M m _) (hg _ (by omega)) _ f (evB M c) (h _ (by omega)) H
  rw [e]
  rfl

end CrystallineSemistableComparison.Pb.Kap.Mo
end
end
end
