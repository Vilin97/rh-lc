module

public import Formalism.LocalToGlobal.GlobalTheory.GL5.PNamed
public import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
public import Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RetieVolTieGAndCdScaleTie
public import Formalism.LocalToGlobal.BesselHermitianTheta.Lemmas
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Retie
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusMassStdAll
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeStabilizerDoubleCosetsClassRestMassStatement
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryVolumeEqRankMassAllSignatures
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicQuotientVolumeEqOfSignatureRankIndep

section

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Glob

theorem volMeas_fundDomain_eq_of_tiedIndep :
    (∀ D : D7, VolTie D → ∀ (W W₀ : HSpace D.host.E) (P Q P₀ Q₀ : ℕ), W.SigOK → W₀.SigOK → (∀ τ, W.sig τ = (P, Q)) → (∀ τ, W₀.sig τ = (P₀, Q₀)) → W.rank = W₀.rank → D.vol W = D.vol W₀) → ∀ D : D7, ∀ (W W₀ : HSpace D.host.E) (P Q P₀ Q₀ : ℕ), W.SigOK → W₀.SigOK → (∀ τ, W.sig τ = (P, Q)) → (∀ τ, W₀.sig τ = (P₀, Q₀)) → W.rank = W₀.rank → ∀ (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram)) (𝓕 : Set (HA (AF D.host.F) D.sp.cm.sig W.gram)) (μ₀ : Measure (HA (AF D.host.F) D.sp.cm.sig W₀.gram)) (𝓕₀ : Set (HA (AF D.host.F) D.sp.cm.sig W₀.gram)), IsVolMeas D W P Q μ → IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W.gram) 𝓕 μ → IsVolMeas D W₀ P₀ Q₀ μ₀ → IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W₀.gram) 𝓕₀ μ₀ → μ 𝓕 = μ₀ 𝓕₀ := by
  intro H D W W₀ P Q P₀ Q₀ hW hW₀ hs hs₀ hr μ 𝓕 μ₀ 𝓕₀ hμ h𝓕 hμ₀ h𝓕₀
  have hT : VolTie (GlobalTheory.Mem.retie D) :=
    Formalism.L2.Theta.VolTieG.volTie (GlobalTheory.Mem.retie_volTieG_and_cdScaleTie D).1
  have e1 : μ 𝓕 = ENNReal.ofReal ((GlobalTheory.Mem.retie D).vol W) :=
    ((hT W P Q hW hs).2 μ hμ).2 𝓕 h𝓕
  have e2 : μ₀ 𝓕₀ = ENNReal.ofReal ((GlobalTheory.Mem.retie D).vol W₀) :=
    ((hT W₀ P₀ Q₀ hW₀ hs₀).2 μ₀ hμ₀).2 𝓕₀ h𝓕₀
  rw [e1, e2, H (GlobalTheory.Mem.retie D) hT W W₀ P Q P₀ Q₀ hW hW₀ hs hs₀ hr]

end GlobalTheory.Glob
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicQuotientVolumeEqOfSignatureRankIndepStatement

section

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adelicQuotientVolume_eq_of_signature_rank_indep : (∀ D : D7, VolTie D → ∀ (W W₀ : HSpace D.host.E) (P Q P₀ Q₀ : ℕ), W.SigOK → W₀.SigOK → (∀ τ, W.sig τ = (P, Q)) → (∀ τ, W₀.sig τ = (P₀, Q₀)) → W.rank = W₀.rank → D.vol W = D.vol W₀) → ∀ D : D7, ∀ (W W₀ : HSpace D.host.E) (P Q P₀ Q₀ : ℕ), W.SigOK → W₀.SigOK → (∀ τ, W.sig τ = (P, Q)) → (∀ τ, W₀.sig τ = (P₀, Q₀)) → W.rank = W₀.rank → ∀ (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram)) (𝓕 : Set (HA (AF D.host.F) D.sp.cm.sig W.gram)) (μ₀ : Measure (HA (AF D.host.F) D.sp.cm.sig W₀.gram)) (𝓕₀ : Set (HA (AF D.host.F) D.sp.cm.sig W₀.gram)), IsVolMeas D W P Q μ → IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W.gram) 𝓕 μ → IsVolMeas D W₀ P₀ Q₀ μ₀ → IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W₀.gram) 𝓕₀ μ₀ → μ 𝓕 = μ₀ 𝓕₀ := by
  first | exact @GlobalTheory.Glob.volMeas_fundDomain_eq_of_tiedIndep | exact GlobalTheory.Glob.volMeas_fundDomain_eq_of_tiedIndep | (intros; apply GlobalTheory.Glob.volMeas_fundDomain_eq_of_tiedIndep <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumInvCardStabEq

section

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeightedDoubleCoset

def stabConjEquiv {G : Type} [Group G] (Γ K : Subgroup G) (g : G) (γ₀ : Γ) (k : K) :
    Unfold.stab Γ K ((γ₀ : G) * g * k) ≃ Unfold.stab Γ K g where
  toFun δ := ⟨γ₀⁻¹ * δ.1 * γ₀, by
    have h := K.mul_mem (K.mul_mem k.2 δ.2) (K.inv_mem k.2)
    simp only [Unfold.stab, Set.mem_setOf_eq, Subgroup.coe_mul, Subgroup.coe_inv] at h ⊢
    convert h using 1; group⟩
  invFun δ := ⟨γ₀ * δ.1 * γ₀⁻¹, by
    have h := K.mul_mem (K.mul_mem (K.inv_mem k.2) δ.2) k.2
    simp only [Unfold.stab, Set.mem_setOf_eq, Subgroup.coe_mul, Subgroup.coe_inv] at h ⊢
    convert h using 1; group⟩
  left_inv δ := by ext; simp [mul_assoc]
  right_inv δ := by ext; simp [mul_assoc]

theorem card_stab_eq {G : Type} [Group G] (Γ K : Subgroup G) (g : G) (γ₀ : Γ) (k : K) :
    Nat.card (Unfold.stab Γ K ((γ₀ : G) * g * k)) = Nat.card (Unfold.stab Γ K g) :=
  Nat.card_congr (stabConjEquiv Γ K g γ₀ k)

theorem sum_inv_card_stab_eq : ∀ (G : Type) [Group G] (Γ K : Subgroup G) (n m : ℕ) (g : Fin n → G) (g' : Fin m → G), (∀ x : G, ∃ i, ∃ γ : Γ, ∃ k : K, x = (γ : G) * g i * k) → (∀ i j (γ γ' : Γ) (k k' : K), (γ : G) * g i * k = (γ' : G) * g j * k' → i = j) → (∀ x : G, ∃ i, ∃ γ : Γ, ∃ k : K, x = (γ : G) * g' i * k) → (∀ i j (γ γ' : Γ) (k k' : K), (γ : G) * g' i * k = (γ' : G) * g' j * k' → i = j) → ∑ i, ((Nat.card (Unfold.stab Γ K (g i)) : ℝ))⁻¹ = ∑ j, ((Nat.card (Unfold.stab Γ K (g' j)) : ℝ))⁻¹ := by
  intro G _ Γ K n m g g' hcov hdisj hcov' hdisj'
  choose e γe ke he using fun i => hcov' (g i)
  choose f γf kf hf using fun j => hcov (g' j)
  have hfe : ∀ i, f (e i) = i := by
    intro i
    symm
    refine hdisj i (f (e i)) 1 (γe i * γf (e i)) 1 (kf (e i) * ke i) ?_
    have h1 := he i
    rw [hf (e i)] at h1
    simp only [OneMemClass.coe_one, one_mul, mul_one, Subgroup.coe_mul]
    simpa only [mul_assoc] using h1
  have hef : ∀ j, e (f j) = j := by
    intro j
    symm
    refine hdisj' j (e (f j)) 1 (γf j * γe (f j)) 1 (ke (f j) * kf j) ?_
    have h1 := hf j
    rw [he (f j)] at h1
    simp only [OneMemClass.coe_one, one_mul, mul_one, Subgroup.coe_mul]
    simpa only [mul_assoc] using h1
  let σ : Fin n ≃ Fin m := ⟨e, f, hfe, hef⟩
  refine Fintype.sum_equiv σ _ _ (fun i => ?_)
  show ((Nat.card (Unfold.stab Γ K (g i)) : ℝ))⁻¹ = ((Nat.card (Unfold.stab Γ K (g' (e i))) : ℝ))⁻¹
  rw [he i, card_stab_eq]

end GlobalTheory.WeightedDoubleCoset
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassNumberFiniteAndGenusMass

section

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ClassNumberMass

theorem classFin_and_classMass : ∀ D : D7, ClassFin D ∧ ClassMass D := by
  intro D
  refine ⟨fun W hW hsig => ?_, fun W hW hsig n g hcov hdisj => ?_⟩
  · obtain ⟨n, g, hcov, hdisj, _⟩ := GlobalTheory.T.lattice_stabilizer_doubleCosets_classRest_mass D W hW hsig
    exact ⟨n, g, hcov, hdisj⟩
  · obtain ⟨m, g', hcov', hdisj', hsum⟩ := GlobalTheory.T.lattice_stabilizer_doubleCosets_classRest_mass D W hW hsig
    rw [← hsum]
    exact GlobalTheory.WeightedDoubleCoset.sum_inv_card_stab_eq _ _ _ n m g g' hcov hdisj hcov' hdisj'

end GlobalTheory.ClassNumberMass
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassNumberFiniteAndGenusMassStatement

section

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.classNumber_finite_and_genusMass : ∀ D : D7, ClassFin D ∧ ClassMass D := by
  first | exact @GlobalTheory.ClassNumberMass.classFin_and_classMass | exact GlobalTheory.ClassNumberMass.classFin_and_classMass | (intros; apply GlobalTheory.ClassNumberMass.classFin_and_classMass <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianClassNumberItemsAllRanks

section

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem classItemsAt_all : ∀ (D : D7) (n : ℕ), ClassItemsAt D n := fun D n =>
  have h := GlobalTheory.T.classNumber_finite_and_genusMass D
  ⟨genusMassAt_of D (GlobalTheory.genusMassStd_all D) n, classFinAt_of D h.1 n, classMassAt_of D h.2 n⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianClassNumberItemsAllRanksStatement

section

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hermitianClassNumberItems_all_ranks : ∀ (D : D7) (n : ℕ), ClassItemsAt D n := by
  first | exact @GlobalTheory.classItemsAt_all | exact GlobalTheory.classItemsAt_all | (intros; apply GlobalTheory.classItemsAt_all <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryVolumeEqRankMassAllSignaturesStatement

section

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unitary_volume_eq_rank_mass_all_signatures : ∀ D : D7, VolTie D → Conclusion2 D → ∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK → (∀ τ, W.sig τ = (P, Q)) → D.vol W = massI D (P + Q) := by
  first | exact @GlobalTheory.Glob.vol_eq_massI_all_sig | exact GlobalTheory.Glob.vol_eq_massI_all_sig | (intros; apply GlobalTheory.Glob.vol_eq_massI_all_sig <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolumeSignatureIndepAndClassNumberItems

section

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Glob

theorem volSigIndep_and_classItemsAt_of_massRatioUnderVolume (hU : ∀ D : D7, Formalism.MainNotions.RT.MassRatioUnderVolume D) :
    ∀ D : D7, VolSigIndep D ∧ ClassItemsAt D (D.sp.Y 0).rank := by
  intro D
  refine ⟨?_, GlobalTheory.T.hermitianClassNumberItems_all_ranks D _⟩
  have key := GlobalTheory.T.adelicQuotientVolume_eq_of_signature_rank_indep (fun D hT W W₀ P Q P₀ Q₀ hW hW₀ hs hs₀ hr => by
    have h2 : Conclusion2 D := volumeMass_of_unfolding D (hU D hT)
    rw [GlobalTheory.T.unitary_volume_eq_rank_mass_all_signatures D hT h2 W P Q hW hs, GlobalTheory.T.unitary_volume_eq_rank_mass_all_signatures D hT h2 W₀ P₀ Q₀ hW₀ hs₀]
    have e1 := Formalism.BasicNotions.sig_sum W hW D.host.φ₀
    have e2 := Formalism.BasicNotions.sig_sum W₀ hW₀ D.host.φ₀
    rw [hs] at e1
    rw [hs₀] at e2
    simp only at e1 e2
    rw [e1, e2, hr])
  exact key D

end GlobalTheory.Glob
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolumeSignatureIndepAndClassNumberItemsStatement

section

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.volume_signature_indep_and_classNumberItems : (∀ D : D7, Formalism.MainNotions.RT.MassRatioUnderVolume D) → ∀ D : D7, VolSigIndep D ∧ ClassItemsAt D (D.sp.Y 0).rank := by
  first | exact @GlobalTheory.Glob.volSigIndep_and_classItemsAt_of_massRatioUnderVolume | exact GlobalTheory.Glob.volSigIndep_and_classItemsAt_of_massRatioUnderVolume | (intros; apply GlobalTheory.Glob.volSigIndep_and_classItemsAt_of_massRatioUnderVolume <;> assumption)
end
end
