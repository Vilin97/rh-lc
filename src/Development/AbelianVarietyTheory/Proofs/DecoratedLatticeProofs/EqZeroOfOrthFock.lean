module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
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
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthRealHeisenbergTranslatesVacuumOfOrthFockStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HomSymplecticHalfFormAlgebraicLawsContinuous
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaThetaFunctionsOrientedPair
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCoefficientsSeparatingCharactersEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilator
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthAllHeisenbergTranslatesOfOrthRealLatticeVacu

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinOrth

variable {D : D7} {S T : HSp D}

theorem setIntegral_add_right {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure (WO S T))
    [μ.IsAddHaarMeasure] {𝓕 : Set (WO S T)} (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {g : WO S T → E}
    (hg : ∀ γ ∈ ratL T S, ∀ w, g (γ + w) = g w) (u : WO S T) :
    ∫ w in 𝓕, g (w + u) ∂μ = ∫ w in 𝓕, g w ∂μ := by
  have i6 : BorelSpace (WO S T) := ⟨rfl⟩
  have : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  have : Countable (Matrix (Fin T.rank) (Fin S.rank) D.host.E) :=
    inferInstanceAs (Countable (Fin T.rank → Fin S.rank → D.host.E))
  have : Countable (ratL T S) := (Set.countable_range _).to_subtype
  have : MeasurableConstVAdd (ratL T S) (WO S T) := ⟨fun c => (continuous_const.add continuous_id).measurable⟩
  have : VAddInvariantMeasure (ratL T S) (WO S T) μ := ⟨fun c s _ => measure_preimage_add μ (c : WO S T) s⟩
  have hmp : MeasurePreserving (fun w : WO S T => u + w) μ μ := measurePreserving_add_left μ u
  have hemb : MeasurableEmbedding (fun w : WO S T => u + w) := (MeasurableEquiv.addLeft u).measurableEmbedding
  have hpre : 𝓕 = (fun w : WO S T => u + w) ⁻¹' ((fun w : WO S T => -u + w) ⁻¹' 𝓕) := by
    ext w; simp
  have h𝓕' : IsAddFundamentalDomain (ratL T S) ((fun w : WO S T => -u + w) ⁻¹' 𝓕) μ := by
    refine h𝓕.preimage_of_equiv (measurePreserving_add_left μ (-u)).quasiMeasurePreserving
      (e := id) Function.bijective_id fun γ w => ?_
    simp only [id, AddSubgroup.vadd_def, vadd_eq_add]
    abel
  have e1 : ∫ w in 𝓕, g (w + u) ∂μ = ∫ w in (fun w : WO S T => u + w) ⁻¹' ((fun w : WO S T => -u + w) ⁻¹' 𝓕),
      g (u + w) ∂μ := by
    rw [← hpre]; simp_rw [add_comm _ u]
  rw [e1, hmp.setIntegral_preimage_emb hemb]
  exact h𝓕'.setIntegral_eq h𝓕 fun γ w => by rw [AddSubgroup.vadd_def, vadd_eq_add]; exact hg γ γ.2 w

theorem star_mul_self_psi {ψ : AddChar (AF D.host.F) ℂ} (hn : ∀ x, ‖ψ x‖ = 1) (a : AF D.host.F) :
    star (ψ a) * ψ a = 1 := by
  rw [Complex.star_def, Complex.conj_mul', hn]; simp

theorem thPair_heisO {ψ : AddChar (AF D.host.F) ℂ} (hn : ∀ x, ‖ψ x‖ = 1) (μ : Measure (WO S T))
    [μ.IsAddHaarMeasure] {𝓕 : Set (WO S T)} (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {f g : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) (u : WO S T) :
    thPair μ 𝓕 (heisO ψ S T u f) (heisO ψ S T u g) = thPair μ 𝓕 f g := by
  have hs := star_mul_self_psi hn
  unfold thPair
  have e : ∀ w, heisO ψ S T u f w * star (heisO ψ S T u g w) = f (w + u) * star (g (w + u)) := by
    intro w
    simp only [heisO, star_mul']
    linear_combination (f (w + u) * star (g (w + u))) * hs (symplOH S T w u)
  simp_rw [e]
  refine setIntegral_add_right μ h𝓕 (g := fun w => f w * star (g w)) ?_ u
  rintro _ ⟨γ, rfl⟩ w
  change f (ratW T S γ + w) * star (g (ratW T S γ + w)) = f w * star (g w)
  rw [hf.quasi, hg.quasi, star_mul']
  linear_combination (f w * star (g w)) * hs (-(symplOH S T (ratW T S γ) w))

theorem thetaNormSq_heisenbergOp_invariant {ψ : AddChar (AF D.host.F) ℂ} (hn : ∀ x, ‖ψ x‖ = 1) (μ : Measure (WO S T))
    [μ.IsAddHaarMeasure] {𝓕 : Set (WO S T)} (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (u : WO S T) : nrm2 μ 𝓕 (heisO ψ S T u f) = nrm2 μ 𝓕 f := by
  unfold nrm2
  have e : ∀ w, ‖heisO ψ S T u f w‖ ^ 2 = ‖f (w + u)‖ ^ 2 := fun w => by
    simp only [heisO, norm_mul, hn, one_mul]
  simp_rw [e]
  refine setIntegral_add_right μ h𝓕 (g := fun w => ‖f w‖ ^ 2) ?_ u
  rintro _ ⟨γ, rfl⟩ w
  change ‖f (ratW T S γ + w)‖ ^ 2 = ‖f w‖ ^ 2
  rw [hf.quasi, norm_mul, hn, one_mul]

theorem thPair_smul_right (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f g : WO S T → ℂ) (c : ℂ) :
    thPair μ 𝓕 f (c • g) = star c * thPair μ 𝓕 f g := by
  unfold thPair
  rw [← integral_const_mul]
  congr 1; funext w
  simp only [Pi.smul_apply, smul_eq_mul, star_mul']
  ring

theorem orth_all : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ vac, IsVacO ψ θ S T x.s y.s x.L y.L vac → ∀ (v : VolM D T.rank S.rank) f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T x.L y.L fun _ => True) f → (∀ u : WO S T, u.map (finPart D) = 0 → thPair v.μ v.𝓕 f (heisO ψ S T u vac) = 0) → ∀ u : WO S T, thPair v.μ v.𝓕 f (heisO ψ S T u vac) = 0 := by
  intro D ψ θ hθ S T x y hx hy vac hvac v f hf hlat hreal u
  have hψ := hvac.1
  have hn : ∀ a, ‖ψ a‖ = 1 := hψ.1.2.1
  haveI : v.μ.IsAddHaarMeasure := v.covol.1
  have hF : IsAddFundamentalDomain (ratL T S) v.𝓕 v.μ := v.covol.2.1
  have hvt : IsThetaFunO ψ S T vac := hvac.2.theta
  have hvl := hvac.2.lat

  have key : ∀ g : WO S T, heisO ψ S T g f = f → heisO ψ S T g vac = vac → ψ (symplO S T g u) ≠ 1 →
      thPair v.μ v.𝓕 f (heisO ψ S T u vac) = 0 := by
    intro g hgf hgv hne
    have hc : heisO ψ S T g (heisO ψ S T u vac) = ψ (symplO S T g u) • heisO ψ S T u vac := by
      rw [GlobalTheory.SplitScalar.heisO_comm, hgv]
    have e := thPair_heisO hn v.μ hF hf (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hvt u) g
    rw [hgf, hc, thPair_smul_right] at e
    have hne' : star (ψ (symplO S T g u)) ≠ 1 := by
      intro h; apply hne; rw [← star_star (ψ _), h, star_one]
    have h2 : (1 - star (ψ (symplO S T g u))) * thPair v.μ v.𝓕 f (heisO ψ S T u vac) = 0 := by
      linear_combination e.symm
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (Ne.symm hne'))
  by_cases hA1 : ∀ g ∈ latO S T x.L y.L (fun _ => True), ψ (symplO S T (2 • g) u) = 1
  swap
  · push_neg at hA1
    obtain ⟨g, hg, hne⟩ := hA1
    exact key (2 • g) (hlat.1 g hg) (hvl.1 g hg) hne
  by_cases hA2 : ∀ e, IsSplitIdem D e → ∀ g ∈ latO S T x.L y.L (fun _ => True), IsHalf e g →
      ψ (symplO S T g u) = 1
  swap
  · push_neg at hA2
    obtain ⟨e, he, g, hg, hh, hne⟩ := hA2
    exact key g (hlat.2 e he g hg hh) (hvl.2 e he g hg hh) hne

  obtain ⟨ur, uf, hr, hfi, rfl⟩ : ∃ ur uf : WO S T, ur.map (finPart D) = 0 ∧ uf.map (infPart D) = 0 ∧
      u = ur + uf := by
    refine ⟨GlobalTheory.FinTranslate.eInf D • u, (1 - GlobalTheory.FinTranslate.eInf D) • u, ?_, ?_, ?_⟩
    · ext i j; exact GlobalTheory.ThetaClosed.finPart_eInf_smul (u i j)
    · ext i j; exact GlobalTheory.ThetaClosed.infPart_one_sub_eInf_smul (u i j)
    · rw [← add_smul, add_sub_cancel, one_smul]
  have hlf : ∀ g ∈ latO S T x.L y.L (fun _ => True), g.map (infPart D) = 0 := fun g hg =>
    GlobalTheory.SplitScalar.latO_fin hg
  have hsf : ∀ g : WO S T, g.map (infPart D) = 0 → symplO S T g (ur + uf) = symplO S T g uf := by
    intro g hg
    rw [GlobalTheory.LatVac.symplO_add_right, GlobalTheory.SplitScalar.symplO_skew S T ur g, GlobalTheory.SplitScalar.symplO_real_fin S T hr hg,
      neg_zero, zero_add]
  have hv' : IsVacO ψ θ S T x.s y.s x.L y.L (heisO ψ S T uf vac) := by
    have hv2 := hvac
    obtain ⟨-, hinf, hth, hl, hfock, hnorm⟩ := hv2
    refine ⟨hψ, hinf, GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hth uf, ⟨fun g hg => ?_, fun e he g hg hh => ?_⟩,
      fun τ z => ?_, hnorm.1, fun p hp => ?_⟩
    · rw [GlobalTheory.SplitScalar.heisO_comm, hl.1 g hg, ← hsf _ (hlf _ (AddSubgroup.nsmul_mem _ hg 2)), hA1 g hg, one_smul]
    · rw [GlobalTheory.SplitScalar.heisO_comm, hl.2 e he g hg hh, ← hsf _ (hlf g hg), hA2 e he g hg hh, one_smul]
    · have h0 := hfock τ z
      unfold annih at h0 ⊢
      rw [GlobalTheory.FinTranslate.dRho_heisO hinf hfi, GlobalTheory.FinTranslate.dRho_heisO hinf hfi]
      have h1 := congrArg (GlobalTheory.FinTranslate.heisL S T ψ uf) h0
      rw [map_add (f := _), map_smul, map_zero] at h1
      exact h1
    · show nrm2 p.1 p.2 (heisO ψ S T uf vac) = 1
      haveI := hp.1
      rw [thetaNormSq_heisenbergOp_invariant hn p.1 hp.2.1 hth uf]
      exact hnorm.2 p hp
  obtain ⟨c, -, hc⟩ := GlobalTheory.VacUnique.vacUniqueO D ψ θ hψ hθ S T x.s y.s hx.sig hy.sig hx.cart hy.cart x.L y.L
    hx.sd hy.sd vac _ hvac hv'
  have e : heisO ψ S T (ur + uf) vac = c • heisO ψ S T ur vac := by
    rw [GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (GlobalTheory.SplitScalar.symplO_real_fin S T hr hfi), hc,
      GlobalTheory.SplitScalar.heisO_smul]
  rw [e, thPair_smul_right, hreal ur hr, mul_zero]

end GlobalTheory.FinOrth

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthAllHeisenbergTranslatesOfOrthRealLatticeVacuStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.orth_allHeisenbergTranslates_of_orth_real_latticeVacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ vac, IsVacO ψ θ S T x.s y.s x.L y.L vac → ∀ (v : VolM D T.rank S.rank) f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T x.L y.L fun _ => True) f → (∀ u : WO S T, u.map (finPart D) = 0 → thPair v.μ v.𝓕 f (heisO ψ S T u vac) = 0) → ∀ u : WO S T, thPair v.μ v.𝓕 f (heisO ψ S T u vac) = 0 := by
  first | exact @GlobalTheory.FinOrth.orth_all | exact GlobalTheory.FinOrth.orth_all | (intros; apply GlobalTheory.FinOrth.orth_all <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunEqZeroOfOrthHeisenbergTranslates

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaIrred

theorem prod_eq_zero {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} (v : VolM D T.rank S.rank)
    {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g)
    (horth : ∀ u : WO S T, thPair v.μ v.𝓕 f (heisO ψ S T u g) = 0) (u x : WO S T) :
    f x * star (heisO ψ S T u g x) = 0 := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  have hμ : v.μ.IsAddHaarMeasure := v.covol.1
  have h𝓕 : IsAddFundamentalDomain (ratL T S) v.𝓕 v.μ := v.covol.2.1
  obtain ⟨l1, l2, -, l4, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  obtain ⟨hth, hcomp, -⟩ := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  have hu := hth u g hg
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (WO S T) (ratL T S) K hK hKc (ratL T S)
    (fun γ x => ψ (symplO S T x γ))
    (fun γ => by
      have : Continuous fun x : WO S T => symplOH S T x (γ : WO S T) :=
        GlobalTheory.WeilVacMove.continuous_symplOH S T continuous_id' continuous_const
      simp only [← l4]
      exact hψ.1.1.comp (this.add this))
    (fun γ x y => by
      simp only [← l4, l1, AddChar.map_add_eq_mul]
      ring)
    (fun γ γ' x => by
      simp only [← l4, AddSubgroup.coe_add, l2, AddChar.map_add_eq_mul]
      ring)
    (fun x => by
      simp only [← l4, AddSubgroup.coe_zero, GlobalTheory.WeilVacMove.symplOH_zero_right, add_zero, AddChar.map_zero_eq_one])
    (fun γ x => hψ.1.2.1 _)
    (fun x => by
      rw [← GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ S T x]
      exact ⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩)
    v.μ v.𝓕 hμ h𝓕 (fun x => f x * star (heisO ψ S T u g x))
    (hf.cont.mul hu.cont.star)
    (fun γ hγ x => GlobalTheory.ThetaSchur.prod_periodic hψ hf hu hγ x)
    (fun γ => by
      have hneg : ∀ x, symplO S T x ((-γ : ratL T S) : WO S T) = -symplO S T x (γ : WO S T) := by
        intro x
        have h0 := l2 x (γ : WO S T) (-(γ : WO S T))
        rw [add_neg_cancel, GlobalTheory.WeilVacMove.symplOH_zero_right] at h0
        simp only [← l4, AddSubgroup.coe_neg]
        linear_combination (-2 : AF D.host.F) * h0
      have e : (fun x => ψ (symplO S T x γ) * (f x * star (heisO ψ S T u g x))) = fun x =>
          star (ψ (symplOH S T (-(γ : WO S T)) u)) * (f x * star (heisO ψ S T (-(γ : WO S T) + u) g x)) := by
        funext x
        have E := congrFun (hcomp (-(γ : WO S T)) u g) x
        rw [GlobalTheory.ThetaSchur.heisO_rat hu (neg_mem γ.2) x, Pi.smul_apply, smul_eq_mul] at E
        have E' := congrArg star E
        rw [star_mul', star_mul'] at E'
        have hs : star (ψ (-symplO S T x (γ : WO S T))) = ψ (symplO S T x (γ : WO S T)) := by
          have h1 := GlobalTheory.ThetaSchur.mul_star_psi hψ (-symplO S T x (γ : WO S T))
          have h2 : ψ (-symplO S T x (γ : WO S T)) * ψ (symplO S T x (γ : WO S T)) = 1 := by
            rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
          linear_combination ψ (symplO S T x (γ : WO S T)) * h1 - star (ψ (-symplO S T x (γ : WO S T))) * h2
        have hn := hneg x
        simp only [AddSubgroup.coe_neg] at hn
        rw [hn] at E'
        linear_combination (f x) * E' - (f x * star (heisO ψ S T u g x)) * hs
      show ∫ x in v.𝓕, ψ (symplO S T x γ) * (f x * star (heisO ψ S T u g x)) ∂v.μ = 0
      rw [e, integral_const_mul]
      have := horth (-(γ : WO S T) + u)
      unfold thPair at this
      rw [this, mul_zero])
  exact congrFun key x

theorem eq_zero_of_orth_heis : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (v : VolM D T.rank S.rank) (f g : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → g ≠ 0 → (∀ u : WO S T, thPair v.μ v.𝓕 f (heisO ψ S T u g) = 0) → f = 0 := by
  intro D ψ hψ S T v f g hf hg hg0 horth
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hg0
  funext x
  have h := prod_eq_zero hψ v hf hg horth (y - x) x
  have hz : ψ (symplOH S T x (y - x)) ≠ 0 := fun h0 => by
    have := hψ.1.2.1 (symplOH S T x (y - x))
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  simp only [heisO, add_sub_cancel, star_mul'] at h
  rcases mul_eq_zero.1 h with h | h
  · exact h
  · rcases mul_eq_zero.1 h with h | h
    · exact absurd (star_eq_zero.1 h) hz
    · exact absurd (star_eq_zero.1 h) hy

end GlobalTheory.ThetaIrred

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunEqZeroOfOrthHeisenbergTranslatesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaFun_eq_zero_of_orth_heisenbergTranslates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (v : VolM D T.rank S.rank) (f g : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → g ≠ 0 → (∀ u : WO S T, thPair v.μ v.𝓕 f (heisO ψ S T u g) = 0) → f = 0 := by
  first | exact @GlobalTheory.ThetaIrred.eq_zero_of_orth_heis | exact GlobalTheory.ThetaIrred.eq_zero_of_orth_heis | (intros; apply GlobalTheory.ThetaIrred.eq_zero_of_orth_heis <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqZeroOfOrthFock

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockTotal

theorem eq_zero_of_orth_fock : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ vac, IsVacO ψ θ S T x.s y.s x.L y.L vac → ∀ (v : VolM D T.rank S.rank) f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T x.L y.L fun _ => True) f → (∀ P, thPair v.μ v.𝓕 f (pureTensorO ψ θ S T x.s y.s x.B y.B vac P) = 0) → f = 0 := by
  intro D ψ θ hθ S T x y hx hy vac hvac v f hf hlat horth
  have hne : vac ≠ 0 := by
    intro h0
    have h1 := hvac.2.norm.2 (v.μ, v.𝓕) v.covol
    simp [h0, nrm2] at h1
  exact GlobalTheory.T.thetaFun_eq_zero_of_orth_heisenbergTranslates D ψ hvac.1 S T v f vac hf hvac.2.theta hne
    (GlobalTheory.T.orth_allHeisenbergTranslates_of_orth_real_latticeVacuum D ψ θ hθ S T x y hx hy vac hvac v f hf hlat
      (GlobalTheory.T.orth_realHeisenbergTranslates_vacuum_of_orth_fock D ψ θ hθ S T x y hx hy vac hvac v f hf horth))

end GlobalTheory.FockTotal
end
end
end
