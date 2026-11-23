module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeSplitOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
public import Formalism.SatakeDualWeyl.StatementE
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeParametersBoundedLatticeEigenfunctionStatement
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets

-- Source module: Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.SmallRowEigenvalues

section

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SmallBlockEigenvalues

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N

def RowEigSmall {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) :
    Prop :=
  ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ →
    ∀ w : PlE H, IsSplitPl H w → A.unr (A.locW i σ w) →
      ∀ α ∈ A.frobEig (A.locW i σ w), ‖α‖ < ((normV w : ℕ) : ℝ) ^ (((R.t : ℝ) - 1) / 2)

theorem one_lt_normV {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    1 < normV w := by
  unfold normV
  have : Finite (𝓞 E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  have : Nontrivial (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr w.isPrime.ne_top
  exact Finite.one_lt_card

theorem rowEigSmall_of_le {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N)
    (h : ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ →
      ∀ w : PlE H, IsSplitPl H w → A.unr (A.locW i σ w) →
        ∀ α ∈ A.frobEig (A.locW i σ w), ‖α‖ ≤ ((normV w : ℕ) : ℝ) ^ (((R.r : ℝ) - 1) / 2)) :
    RowEigSmall N A := by
  intro i σ hσ w hw hu α hα
  have hrt : R.r < R.t := by have := R.rank_add_five_le; unfold Ranks.r; omega
  refine lt_of_le_of_lt (h i σ hσ w hw hu α hα) ?_
  have h1 : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  have h2 : (R.r : ℝ) < (R.t : ℝ) := by exact_mod_cast hrt
  exact Real.rpow_lt_rpow_of_exponent_lt h1 (by linarith)

end GlobalTheory.IndefiniteRowSideFullHecke.SmallBlockEigenvalues
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeneralLinearTransitiveOnLatticesOverDVR

section

@[expose] public section

open GlobalTheory.LatHecke

namespace GlobalTheory.LatHecke

theorem gl_transitive_lattices : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ), (∀ L : Lat O K r, ∃ g : GL (Fin r) K, glMap g (std O K r).1 = L.1) ∧ ∀ (g : GL (Fin r) K) (L : Lat O K r), (glMap g L.1).IsLattice K := by
  intro O K _ _ _ _ _ _ _ r
  refine ⟨fun L => ?_, fun g L => (glMap_isLattice g L).toIsLattice⟩
  haveI := L.2
  haveI : Module.Free O L.1 := Submodule.IsLattice.free K L.1
  haveI : Module.Finite O L.1 := Module.Finite.iff_fg.2 L.2.fg
  have hr : Module.finrank O L.1 = r := by
    simpa using ((Submodule.IsFullLattice.finrank_eq K L.1).trans (Module.finrank_fintype_fun_eq_card K))
  let b : Module.Basis (Fin r) O L.1 := Module.finBasisOfFinrankEq O L.1 hr
  let c : Module.Basis (Fin r) K (Fin r → K) := b.extendOfIsLattice K
  have hc : ∀ i, c i = (b i : Fin r → K) := fun i => Module.Basis.extendOfIsLattice_apply K b i
  let e : (Fin r → K) ≃ₗ[K] (Fin r → K) := (Pi.basisFun K (Fin r)).equiv c (Equiv.refl _)
  have he : ∀ i, e (Pi.basisFun K (Fin r) i) = c i := fun i => by
    simpa using (Pi.basisFun K (Fin r)).equiv_apply i c (Equiv.refl _)
  let g : GL (Fin r) K :=
    ⟨LinearMap.toMatrix' (e : (Fin r → K) →ₗ[K] (Fin r → K)),
      LinearMap.toMatrix' (e.symm : (Fin r → K) →ₗ[K] (Fin r → K)),
      by rw [← LinearMap.toMatrix'_comp]; simp,
      by rw [← LinearMap.toMatrix'_comp]; simp⟩
  have hg : Matrix.toLin' (g : Matrix (Fin r) (Fin r) K) = (e : (Fin r → K) →ₗ[K] (Fin r → K)) :=
    Matrix.toLin'_toMatrix' _
  refine ⟨g, ?_⟩
  have h1 : Set.range (Subtype.val ∘ b) = L.1.subtype '' Set.range b := by
    rw [← Set.range_comp]; rfl
  change (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map
    ((Matrix.toLin' (g : Matrix (Fin r) (Fin r) K)).restrictScalars O) = L.1
  rw [hg, Submodule.map_span, ← Set.range_comp]
  have h2 : ((e : (Fin r → K) →ₗ[K] (Fin r → K)).restrictScalars O) ∘ (Pi.basisFun K (Fin r))
      = Subtype.val ∘ b := by
    funext i
    simp only [Function.comp_apply, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    rw [he, hc]
  rw [h2, h1, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]

end GlobalTheory.LatHecke
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeneralLinearTransitiveOnLatticesOverDVRStatement

section

@[expose] public section

open GlobalTheory.LatHecke

theorem _root_.GlobalTheory.T.generalLinear_transitive_on_lattices_over_DVR : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ), (∀ L : Lat O K r, ∃ g : GL (Fin r) K, glMap g (std O K r).1 = L.1) ∧ ∀ (g : GL (Fin r) K) (L : Lat O K r), (glMap g L.1).IsLattice K := by
  first | exact @GlobalTheory.LatHecke.gl_transitive_lattices | exact GlobalTheory.LatHecke.gl_transitive_lattices | (intros; apply GlobalTheory.LatHecke.gl_transitive_lattices <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeBoundOfIsometricSphericalGL

section

@[expose] public section

open GlobalTheory.LatHecke

namespace GlobalTheory.LatHecke

theorem satake_bound_of_isometric_spherical : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (ρ : Representation ℂ (GL (Fin r) K) V) (v : V) (α : Multiset ℂ), α.card = r → (∀ g x, ‖ρ g x‖ = ‖x‖) → v ≠ 0 → (∀ g, glMap g (std O K r).1 = (std O K r).1 → ρ g v = v) → (∀ k ≤ r, ∀ s : Finset (GL (Fin r) K), Set.BijOn (fun g => glMap g (std O K r).1) s (Subtype.val '' subElem k (std O K r)) → ∑ g ∈ s, ρ g v = ((((qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) : ℝ) : ℂ) * α.esymm k) • v) → ∀ a ∈ α, ‖a‖ ≤ (qRes O : ℝ) ^ (((r : ℝ) - 1) / 2) := by
  intro O K _ _ _ _ _ _ _ r V _ _ ρ v α hcard hnorm hv hinv heig
  classical
  have hmul : ∀ (a b : GL (Fin r) K) (x : V), ρ (a * b) x = ρ a (ρ b x) := fun a b x => by
    rw [map_mul]; rfl
  have hone : ∀ x : V, ρ 1 x = x := fun x => by
    rw [map_one]; rfl
  choose γ hγ using (GlobalTheory.T.generalLinear_transitive_on_lattices_over_DVR O K r).1
  have hγ' : ∀ L : Lat O K r, γ L • std O K r = L := fun L => Subtype.ext (hγ L)
  let φ : Lat O K r → V := fun L => ρ (γ L) v

  have hφ : ∀ g : GL (Fin r) K, φ (g • std O K r) = ρ g v := by
    intro g
    have hfix : ((γ (g • std O K r))⁻¹ * g) • std O K r = std O K r := by
      rw [mul_smul, inv_smul_eq_iff, hγ']
    have h1 : ρ ((γ (g • std O K r))⁻¹ * g) v = v :=
      hinv _ (congrArg Subtype.val hfix)
    have h2 : ρ g v = ρ (γ (g • std O K r) * ((γ (g • std O K r))⁻¹ * g)) v := by
      rw [mul_inv_cancel_left]
    change ρ (γ (g • std O K r)) v = ρ g v
    rw [h2, hmul, h1]
  have hφg : ∀ (g : GL (Fin r) K) (M : Lat O K r), φ (g • M) = ρ g (φ M) := by
    intro g M
    have h1 : g • M = (g * γ M) • std O K r := by rw [mul_smul, hγ']
    rw [h1, hφ, hmul]
  have hstd : φ (std O K r) = v := by
    have := hφ 1
    rwa [one_smul, hone] at this
  refine GlobalTheory.T.satakeParameters_bounded_lattice_eigenfunction O K r V φ α ‖v‖ hcard ?_ ?_ ?_
  · intro h
    exact hv (by rw [← hstd, h]; rfl)
  · intro L
    exact (hnorm _ _).le
  · intro k hk L

    have h0 : heckeElem k φ (std O K r)
        = ((((qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) : ℝ) : ℂ) * α.esymm k) • v := by
      rw [heckeElem_eq_sum, ← heig k hk ((subElem_finite k (std O K r)).toFinset.image γ)]
      · rw [Finset.sum_image]
        intro M _ M' _ h
        rw [← hγ' M, ← hγ' M', h]
      · refine ⟨?_, ?_, ?_⟩
        · intro g hg
          obtain ⟨M, hM, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hg)
          exact ⟨M, (Set.Finite.mem_toFinset _).1 hM, (hγ M).symm⟩
        · intro g hg g' hg' h
          obtain ⟨M, hM, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hg)
          obtain ⟨M', hM', rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hg')
          have h' : M = M' := Subtype.ext (by simpa only [hγ] using h)
          rw [h']
        · rintro _ ⟨M, hM, rfl⟩
          exact ⟨γ M, Finset.mem_coe.2 (Finset.mem_image.2
            ⟨M, (Set.Finite.mem_toFinset _).2 hM, rfl⟩), hγ M⟩

    have h1 : heckeElem k φ L = ρ (γ L) (heckeElem k φ (std O K r)) := by
      conv_lhs => rw [← hγ' L]

      rw [heckeElem_smul, heckeElem_eq_sum, heckeElem_eq_sum, map_sum]
      exact Finset.sum_congr rfl fun M _ => hφg _ _
    rw [h1, h0, map_smul]
end GlobalTheory.LatHecke
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeBoundOfIsometricSphericalGLStatement

section

@[expose] public section

open GlobalTheory.LatHecke

theorem _root_.GlobalTheory.T.satake_bound_of_isometric_sphericalGL : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (ρ : Representation ℂ (GL (Fin r) K) V) (v : V) (α : Multiset ℂ), α.card = r → (∀ g x, ‖ρ g x‖ = ‖x‖) → v ≠ 0 → (∀ g, glMap g (std O K r).1 = (std O K r).1 → ρ g v = v) → (∀ k ≤ r, ∀ s : Finset (GL (Fin r) K), Set.BijOn (fun g => glMap g (std O K r).1) s (Subtype.val '' subElem k (std O K r)) → ∑ g ∈ s, ρ g v = ((((qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) : ℝ) : ℂ) * α.esymm k) • v) → ∀ a ∈ α, ‖a‖ ≤ (qRes O : ℝ) ^ (((r : ℝ) - 1) / 2) := by
  first | exact @GlobalTheory.LatHecke.satake_bound_of_isometric_spherical | exact GlobalTheory.LatHecke.satake_bound_of_isometric_spherical | (intros; apply GlobalTheory.LatHecke.satake_bound_of_isometric_spherical <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.RpowNegLeNormOfComponent

section

@[expose] public section

noncomputable section

namespace GlobalTheory.RowSatakeBound

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.LatHecke

section Local

variable (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K]

def IsUnitarySatake (r : ℕ) (β : Multiset ℂ) : Prop :=
  β.card = r ∧
  ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V)
    (ρ : Representation ℂ (GL (Fin r) K) V) (v : V),
    (∀ g x, ‖ρ g x‖ = ‖x‖) ∧ v ≠ 0 ∧
    (∀ g, glMap g (std O K r).1 = (std O K r).1 → ρ g v = v) ∧
    ∀ k ≤ r, ∀ s : Finset (GL (Fin r) K),
      Set.BijOn (fun g => glMap g (std O K r).1) s (Subtype.val '' subElem k (std O K r)) →
      ∑ g ∈ s, ρ g v =
        ((((qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) : ℝ) : ℂ) * β.esymm k) • v

variable {O K}

theorem IsUnitarySatake.norm_le {r : ℕ} {β : Multiset ℂ} (h : IsUnitarySatake O K r β) :
    ∀ b ∈ β, ‖b‖ ≤ (qRes O : ℝ) ^ (((r : ℝ) - 1) / 2) := by
  obtain ⟨hc, V, _, _, ρ, v, hρ, hv, hfix, hT⟩ := h
  exact GlobalTheory.T.satake_bound_of_isometric_sphericalGL O K r V ρ v β hc hρ hv hfix hT

end Local

section Completion

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem finite_residue : Finite (IsLocalRing.ResidueField (w.adicCompletionIntegers E)) :=
  Formalism.UG.P.tjcosets_finite w

theorem qRes_eq_normV [Finite (IsLocalRing.ResidueField (w.adicCompletionIntegers E))] :
    qRes (w.adicCompletionIntegers E) = normV w := by
  unfold qRes normV
  rw [Formalism.UG.P.tjcosets_card_residue, Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

def IsUnitarySatakeAt (r : ℕ) (β : Multiset ℂ) : Prop :=
  haveI := finite_residue w
  IsUnitarySatake (w.adicCompletionIntegers E) (w.adicCompletion E) r β

variable {w}

theorem IsUnitarySatakeAt.norm_le {r : ℕ} {β : Multiset ℂ} (h : IsUnitarySatakeAt w r β) :
    ∀ b ∈ β, ‖b‖ ≤ ((normV w : ℕ) : ℝ) ^ (((r : ℝ) - 1) / 2) := by
  have := finite_residue w
  rw [← qRes_eq_normV w]
  exact IsUnitarySatake.norm_le h

end Completion

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def UnitarySphericalComponent : Prop :=
  ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ →
    ∀ w : PlE H, IsSplitPl H w → A.unr (A.locW i σ w) →
      IsUnitarySatakeAt w R.r ((A.frobEig (A.locW i σ w)).map (·⁻¹)) ∧
      IsUnitarySatakeAt w R.r (A.frobEig (A.locW i σ w))

theorem rowSizeLe_of_component (h : UnitarySphericalComponent N A) :
    GlobalTheory.ThetaExh.RowSizeLe N A :=
  fun i σ hσ w hw hu => (h i σ hσ w hw hu).2.norm_le

theorem rowEigSmall_of_component : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R)
    (N : NData R H what₂) (A : NAut N),
    UnitarySphericalComponent N A → GlobalTheory.IndefiniteRowSideFullHecke.SmallBlockEigenvalues.RowEigSmall N A :=
  fun _ _ _ N A h => GlobalTheory.IndefiniteRowSideFullHecke.SmallBlockEigenvalues.rowEigSmall_of_le N A (rowSizeLe_of_component N A h)

theorem rowSize_of_component (h : UnitarySphericalComponent N A) : GlobalTheory.ThetaExh.RowSize N A :=
  rowEigSmall_of_component _ _ _ N A h

end GlobalTheory.RowSatakeBound
end
end
end
