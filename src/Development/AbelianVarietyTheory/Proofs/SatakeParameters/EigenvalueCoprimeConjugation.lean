import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition

noncomputable section

namespace GlobalTheory.Proof.EigenvalueCoprimeConjugation

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual Formalism.CyclotomicNorms ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels GlobalTheory.WeilDeligne GlobalTheory.IndefiniteRowSideFullHecke.TameEigenvaluesTypePrimes

variable (D : D7)

theorem normV_plGw (k : Fin 2) (v : D.nd.PlG k) : normV (D.naut.plGw k v) = D.host.g k :=
  normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) (D.naut.plGw_over k v)

end GlobalTheory.Proof.EigenvalueCoprimeConjugation

end
