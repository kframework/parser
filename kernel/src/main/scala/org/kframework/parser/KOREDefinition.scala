package org.kframework.parser

import org.kframework.minikore.interfaces.pattern._
import org.kframework.minikore.interfaces.build.Builders

case class KarserDSL(b: Builders) {

  val outerUtils = org.kframework.minikore.MiniKoreOuterUtils(b)
  val meta = org.kframework.minikore.MiniKoreMeta(b)

  import org.kframework.minikore.implementation.MiniKore.{Definition, Module, Sentence, Import, SymbolDeclaration, Attributes, Rule}
  import org.kframework.minikore.implementation.MiniKoreDSL._
  import b._
  import outerUtils._
  import meta._

  // Productions
  // ===========

  trait ProductionItem
  case class Regex(regex: String)      extends ProductionItem
  case class Terminal(name: String)    extends ProductionItem
  case class NonTerminal(sort: String) extends ProductionItem

  implicit def asTerminal(name: String): Terminal     = Terminal(name)
  implicit def asNonTerminal(sort: Sort): NonTerminal = NonTerminal(sort.str)

  val KTerminal      = Symbol("#Terminal")
  val KRegexTerminal = Symbol("#RegexTerminal")
  val KNonTerminal   = Symbol("#NonTerminal")
  val KProduction    = Symbol("#Production")

  // TODO: We need to handle regexes better (precede/follow)
  val upProductionItem: ProductionItem => Application = {
    case Terminal(term)    => Application(KTerminal, Seq(DomainValue(KValue, term)))
    case Regex(str)        => Application(KRegexTerminal, Seq(DomainValue(KValue, "#"), DomainValue(KValue, str), DomainValue(KValue, "#")))
    case NonTerminal(sort) => Application(KNonTerminal, Seq(DomainValue(KValue, sort)))
  }

  val downProductionItem: Pattern => ProductionItem = {
    case Application(`KTerminal`, DomainValue(`KValue`, term) :: Nil)                                                                          => Terminal(term)
    case Application(`KRegexTerminal`, DomainValue(`KValue`, precede) :: DomainValue(`KValue`, regex) :: DomainValue(`KValue`, follow) :: Nil) => Regex(precede + regex + follow)
    case Application(`KNonTerminal`, DomainValue(`KValue`, sort) :: Nil)                                                                       => NonTerminal(sort)
  }

  // TODO: This should be more careful with KTerminal and KRegexTermial to take into account precede and follow clauses
  val productionAsSymbol: ProductionItem => String = {
    case Terminal(term)    => term
    case Regex(regex)      => "r\"" + regex + "\""
    case NonTerminal(sort) => "_"
  }

  def mkString(pis: Seq[ProductionItem]): String  = (pis map productionAsSymbol).mkString
  def mkArgs(pis: Seq[ProductionItem]): Seq[Sort] = pis collect { case NonTerminal(sort) => Sort(sort) }

  // Attributes
  // ==========

  val KLabel = Symbol("#Label")

  implicit def asAttribute(name: String): Application = Application(Symbol(name), Seq.empty)

  def kSymbol(symbol: Symbol): Application               = Application(KLabel, Seq(DomainValue(KValue, symbol.str)))
  def kProduction(pis: Seq[ProductionItem]): Application = Application(KProduction, pis map upProductionItem)
  def production(pis: ProductionItem*): Application      = kProduction(pis)
  //def priority(priorities: Seq[Pattern]): Application = Application(KSyntaxPriority, priorities)
  //def kpriority(priorities: Seq[String]*): Application       = priority(Seq(Application(KPriorityItems, priorities map upSymbolList)))

  def getKLabel(atts: Attributes): Option[String] = getAttributeKey(KLabel, atts) match {
    case Seq(Seq(DomainValue(`KValue`, value))) => Some(value)
    case _                                      => None
  }

  // Syntax Declaration
  // ==================

  case class syntax(sort: Sort, pis: Seq[ProductionItem] = Seq.empty) {
    def is(pis: ProductionItem*): syntax = syntax(sort, pis)
    def att(atts: Pattern*): SymbolDeclaration = SymbolDeclaration(sort, Symbol(getKLabel(atts).getOrElse(mkString(pis))), mkArgs(pis), atts :+ kProduction(pis))
  }
  // TODO: For some reason this implicit conversion isn't working
  implicit def asSymbolDeclaration(s: syntax): SymbolDeclaration = s.att()
}


case class KOREDefinition(b: Builders) {

  val meta = org.kframework.minikore.MiniKoreMeta(b)
  val karserDsl = KarserDSL(b)

  import org.kframework.minikore.converters.KoreToMini.{iMainModule, iEntryModules}
  import org.kframework.minikore.implementation.MiniKore.Module
  import org.kframework.minikore.implementation.MiniKoreDSL._
  import b._
  import meta._
  import karserDsl._

  // TODO: GRRRRRRRR, these should be coming from meta._, why isn't that working?
  val KSymbolList   = Symbol("#SymbolList")
  val KSymbolListMt = Symbol("#.SymbolList")

  // KTOKENS
  // =======

  val KRegexSymbol        = "[A-Za-z0-9\\.@#\\-]+"
  val KRegexSymbolEscaped = "`[^\n\r\t\f]+`"
  val KRegexString        = "[\"](([^\n\r\t\f\"\\\\])|([\\\\][nrtf\"\\\\])|([\\\\][x][0-9a-fA-F]{2})|([\\\\][u][0-9a-fA-F]{4})|([\\\\][U][0-9a-fA-F]{8}))*[\"]"

  val SSymbol     = Sort("Symbol")
  val SSymbolList = Sort("SymbolList")
  val SString     = Sort("String")

  val KTOKENS: Module = module("KTOKENS",
    syntax(SSymbol) is Regex(KRegexSymbol)        att("token"),
    syntax(SSymbol) is Regex(KRegexSymbolEscaped) att("token"),

    syntax(SSymbolList) is ""                          att(kSymbol(KSymbolListMt)),
    syntax(SSymbolList) is SSymbol                     att(),
    syntax(SSymbolList) is (SSymbol, ",", SSymbolList) att(kSymbol(KSymbolList)),

    syntax(SString) is Regex(KRegexString) att("token")
  )

  // KPATTERN
  // ========

  val SVariable    = Sort("Variable")
  val SPattern     = Sort("Pattern")
  val SPatternList = Sort("PatternList")

  val KPATTERN: Module = module("KPATTERN",
    imports("KTOKENS"),

    syntax(SVariable) is (SSymbol, ":", SSymbol) att(kSymbol(KVariable)),

    syntax(SPattern) is SVariable           att(),
    syntax(SPattern) is Regex(KRegexSymbol) att("token"),

    syntax(SPattern) is "top" att(kSymbol(KTop)),
    syntax(SPattern) is "bot" att(kSymbol(KBottom)),

    syntax(SPattern) is (SPattern, "/\\", SPattern) att(kSymbol(KAnd)),
    syntax(SPattern) is (SPattern, "\\/", SPattern) att(kSymbol(KOr)),
    syntax(SPattern) is ("~", SPattern)             att(kSymbol(KNot)),

    syntax(SPattern) is (SPattern, "->", SPattern)      att(kSymbol(KImplies)),
    syntax(SPattern) is ("E", SVariable, ".", SPattern) att(kSymbol(KExists)),
    syntax(SPattern) is ("A", SVariable, ".", SPattern) att(kSymbol(KForAll)),

    syntax(SPattern) is ("next", SPattern)         att(kSymbol(KNext)),
    syntax(SPattern) is (SPattern, "=>", SPattern) att(kSymbol(KRewrite)),
    syntax(SPattern) is (SPattern, "==", SPattern) att(kSymbol(KEquals)),

    syntax(SPattern) is (SSymbol, "(", SPatternList, ")") att(kSymbol(KApplication)),

    syntax(SPatternList) is ""                            att(kSymbol(KPatternListMt)),
    syntax(SPatternList) is SPattern                      att(),
    syntax(SPatternList) is (SPattern, ",", SPatternList) att(kSymbol(KPatternList))
  )

  // KSENTENCE
  // =========

  val SAttributes   = Sort("Attributes")
  val SSentence     = Sort("Sentence")
  val SSentenceList = Sort("SentenceList")

  val KSENTENCE: Module = module("KSENTENCE",
    imports("KPATTERN"),

    syntax(SAttributes) is ""                       att(kSymbol(KAttributesMt)),
    syntax(SAttributes) is ("[", SPatternList, "]") att(kSymbol(KAttributes)),

    syntax(SSentence) is ("imports", SSymbol, SAttributes)                                      att(kSymbol(KImport)),
    syntax(SSentence) is ("syntax", SSymbol, ":=", SSymbol, "(", SSymbolList, ")", SAttributes) att(kSymbol(KSymbolDeclaration)),
    syntax(SSentence) is ("rule", SPattern, SAttributes)                                        att(kSymbol(KRule)),

    syntax(SSentenceList) is SSentence                  att(),
    syntax(SSentenceList) is ""                         att(kSymbol(KSentenceListMt)),
    syntax(SSentenceList) is (SSentence, SSentenceList) att(kSymbol(KSentenceList))
  )

  // KDEFINITION
  // ===========

  val SModule     = Sort("Module")
  val SModuleList = Sort("ModuleList")
  val SDefinition = Sort("Definition")

  val KDEFINITION: Module = module("KDEFINITION",
    imports("KSENTENCE"),

    syntax(SModule) is ("module", SSymbol, SSentenceList, "endmodule", SAttributes) att(kSymbol(KModule)),

    syntax(SModuleList) is ""                     att(kSymbol(KModuleListMt)),
    syntax(SModuleList) is (SModule, SModuleList) att(kSymbol(KModuleList)),

    syntax(SDefinition) is (SAttributes, SModuleList) att(kSymbol(KDefinition))
  )

  // KORE
  // ====

  val KORE = definition(KTOKENS, KPATTERN, KSENTENCE, KDEFINITION) att (Application(iMainModule, Seq(DomainValue(KValue, "KDEFINITION"))), Application(iEntryModules, Seq(DomainValue(KValue, "KDEFINITION"))))
}
