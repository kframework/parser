package org.kframework.parser

import org.kframework.attributes.Source
import org.kframework.parser.concrete2kore.ParseInModule
import org.junit.Test
import org.junit.Assert._
import org.kframework.kore.ADT.SortLookup

import org.kframework.minikore.interfaces.pattern._
import org.kframework.minikore.interfaces.build.Builders

import org.kframework.minikore.converters.KoreToMini
import org.kframework.minikore.converters.KoreToMini._
import org.kframework.minikore.converters.MiniToKore
import org.kframework.minikore.converters.MiniToKore._
import org.kframework.minikore.implementation.MiniKore.{Definition, Module, Sentence, Import, SortDeclaration, SymbolDeclaration, Attributes, Rule, Axiom}

import org.kframework.minikore.implementation.MiniKoreDSL._

object ExpDefinition {

  val b: Builders = org.kframework.minikore.implementation.DefaultBuilders
  val karserDsl = KarserDSL(b)
  val minikoreMeta = org.kframework.minikore.MiniKoreMeta(b)

  import b._
  import karserDsl._
  import minikoreMeta._

  val expString =
    """
      [ #MainModule(EXP)
      , #EntryModules(EXP)
      ]

      module EXP
        syntax Exp ::= "0" [kSymbol(0)]
        syntax Exp ::= "1" [kSymbol(1)]
        syntax Exp ::= "2" [kSymbol(2)]
        syntax Exp ::= "3" [kSymbol(3)]
        syntax Exp ::= "4" [kSymbol(4)]
        syntax Exp ::= "5" [kSymbol(5)]
        syntax Exp ::= "6" [kSymbol(6)]
        syntax Exp ::= "7" [kSymbol(7)]
        syntax Exp ::= "8" [kSymbol(8)]
        syntax Exp ::= "9" [kSymbol(9)]

        syntax Exp ::= Exp "+" Exp [kSymbol(p), plus]
        syntax Exp ::= Exp "-" Exp [minus, kSymbol(m)]
        syntax Exp ::= Exp "*" Exp [kSymbol(t), times]
        syntax Exp ::= Exp "/" Exp [kSymbol(d), div]

        rule p(3, 3) => 6
        rule m(9, 4) => 5
        rule t(7, 0) => 0

        rule 2 + 2 => 4
        rule 6 / 3 => 2
      endmodule
    """

  val Exp = Sort("Exp")
  val EXP: Module = module("EXP",
    syntax(Exp) is "0" att(kSymbol("0")),
    syntax(Exp) is "1" att(kSymbol("1")),
    syntax(Exp) is "2" att(kSymbol("2")),
    syntax(Exp) is "3" att(kSymbol("3")),
    syntax(Exp) is "4" att(kSymbol("4")),
    syntax(Exp) is "5" att(kSymbol("5")),
    syntax(Exp) is "6" att(kSymbol("6")),
    syntax(Exp) is "7" att(kSymbol("7")),
    syntax(Exp) is "8" att(kSymbol("8")),
    syntax(Exp) is "9" att(kSymbol("9")),

    syntax(Exp) is (Exp, "+", Exp) att(kSymbol("p"), "plus"),
    syntax(Exp) is (Exp, "-", Exp) att("minus", kSymbol("m")),
    syntax(Exp) is (Exp, "*", Exp) att(kSymbol("t"), "times"),
    syntax(Exp) is (Exp, "/", Exp) att(kSymbol("d"), "div"),

    // priority( >("p", "t") , >("m", "d") ),
    rule(term("p", term("3"), term("3")), term("6")),
    rule(term("m", term("9"), term("4")), term("5")),
    rule(term("t", term("7"), term("0")), term("0")),

    rule(term("p", term("2"), term("2")), term("4")),
    rule(term("d", term("6"), term("3")), term("2"))
  )

  val EXP_DEF = definition(EXP) att(Application(iMainModule, Seq(DomainValue(KValue, "EXP"))), Application(iEntryModules, Seq(DomainValue(KValue, "EXP"))))
}

class ParserBootstrapTest {

  val b: Builders = org.kframework.minikore.implementation.DefaultBuilders
  val karserDsl: KarserDSL = KarserDSL(b)
  val minikoreMeta = org.kframework.minikore.MiniKoreMeta(b)
  val kore = org.kframework.parser.KOREDefinition(b)
  val ekore = org.kframework.parser.EKOREDefinition(b)
  val patternUtils = org.kframework.minikore.MiniKorePatternUtils(b)

  import b._
  import karserDsl._
  import minikoreMeta._
  import kore._
  import ekore._
  import patternUtils._

  val miniDef = MiniToKore(toKoreEncodingDef(EKORE))
  val mainMod = miniDef.mainModule
  val kParser = new ParseInModule(mainMod)

  def runParser(parser: ParseInModule, toParse: String, parseAs: String): Pattern =
    parser.parseString(toParse, SortLookup(parseAs), Source(""))._1 match {
      case Right(x) => KoreToMini(x)
      case Left(y) => throw new Error("runParser error: " + y.toString)
    }
  def parseK(toParse: String, parseAs: String): Pattern = runParser(kParser, toParse, parseAs)
  def parsePrettySentences(input: String): Seq[Pattern] = flattenBySymbols(KSentenceList, KSentenceListMt)(preProcess(parseK(input, "KSentenceList"))) flatMap desugarPrettySentence

  // TODO: won't pass because priorities are generated
  def kdefFixpoint(): Unit = {
    val KORE_STRING = io.Source.fromFile("src/test/scala/org/kframework/parser/kore.k").mkString
    val downed      = downDefinition(ekoreToKore(preProcess(parseK(KORE_STRING, "KDefinition"))))
    assertEquals(KORE, downed)
  }

  @Test def concreteAndAbstractSentencesMatch(): Unit = {
    val Exp  = Sort("Exp")
    val Stmt = Sort("Stmt")
    val sentenceTests: Seq[(Sentence, String)]
        = Seq( (symbol(Exp, "mystmt", Stmt)                 , """syntax Exp := mystmt(Stmt)"""                                                                       )
             , (symbol(Exp, "_", Stmt) att production(Stmt) , """syntax Exp ::= Stmt"""                                                                              )
             , (syntax(Exp) is Stmt att kSymbol("mystmt")   , """syntax Exp := mystmt(Stmt) [kSymbol(mystmt), KProduction(KNonTerminal@K-PRETTY-PRODUCTION(Stmt))]""")
             , (syntax(Exp) is Stmt                         , """syntax Exp ::= Stmt"""                                                                              )
             , (syntax(Exp) is Stmt att kSymbol("mystmt")   , """syntax Exp ::= Stmt [kSymbol(mystmt)]"""                                                            )
             , (syntax(Exp) is ("true", Stmt)               , """syntax Exp ::= "true" Stmt"""                                                                       )
             , (syntax(Exp) is Regex("[^ \n\r\t]+")         , """syntax Exp ::= r"[^ \n\r\t]+""""                                                                    )
             , (syntax(Exp) is Regex(" a\n\r\tb")           , """syntax Exp ::= r" a\n\r\tb""""                                                                      )
             , (syntax(Exp) is Regex("`[^ a\n\r\tb]+`")     , """syntax Exp ::= r"`[^ a\n\r\tb]+`""""                                                                )
             )


    sentenceTests foreach { sentStr => assertEquals(sentStr._1, downSentence(desugarPrettySentence(preProcess(parseK(sentStr._2, "KSentence"))) head)) }
  }

  @Test def multipleProductions(): Unit = {
    val prettyTests: Seq[(String, String)]
        = Seq( ("""syntax Exp ::= "true"                         syntax Exp ::= Exp"""                            , """syntax Exp ::= "true"                         | Exp"""                           )
             , ("""syntax Exp ::= Exp "+" Exp                    syntax Exp ::= Exp "/" Exp [kSymbol(division)]""" , """syntax Exp ::= Exp "+" Exp                    | Exp "/" Exp [kSymbol(division)]""")
             , ("""syntax Exp ::= "true" Exp [kSymbol(withTrue)]  syntax Exp ::= "not" Exp Exp "plus" Exp"""       , """syntax Exp ::= "true" Exp [kSymbol(withTrue)]  | "not" Exp Exp "plus" Exp"""      )
             , ("""syntax Exp ::= Exp "+" Exp [kSymbol(addition)] syntax Exp ::= Exp "/" Exp [kSymbol(division)]""" , """syntax Exp ::= Exp "+" Exp [kSymbol(addition)] | Exp "/" Exp [kSymbol(division)]""")
             )

    def stripPriorities(input: Seq[Pattern]): Seq[Pattern] = input collect { case a@Application(KSymbolDeclaration, _) => a }

    prettyTests foreach { strings => assertEquals(parsePrettySentences(strings._1) map downSentence, stripPriorities(parsePrettySentences(strings._2)) map downSentence) }
  }

  @Test def prioritiesTest(): Unit = {
    val prioritiesTests: Seq[(String, String)]
        = Seq( ("""syntax Exp ::= "true" syntax Exp ::= Exp "+" Exp [kSymbol(p)] syntax Exp ::= Exp "/" Exp [kSymbol(d)] syntax priority true , p , d""" , """syntax Exp ::= "true" | Exp "+" Exp [kSymbol(p)] | Exp "/" Exp [kSymbol(d)]""")
             , ("""syntax Exp ::= "true" syntax Exp ::= Exp "+" Exp [kSymbol(p)] syntax Exp ::= Exp "/" Exp [kSymbol(d)] syntax priority true > p , d""" , """syntax Exp ::= "true" > Exp "+" Exp [kSymbol(p)] | Exp "/" Exp [kSymbol(d)]""")
             , ("""syntax Exp ::= "true" syntax Exp ::= Exp "+" Exp [kSymbol(p)] syntax Exp ::= Exp "/" Exp [kSymbol(d)] syntax priority true , p > d""" , """syntax Exp ::= "true" | Exp "+" Exp [kSymbol(p)] > Exp "/" Exp [kSymbol(d)]""")
             , ("""syntax Exp ::= "true" syntax Exp ::= Exp "+" Exp [kSymbol(p)] syntax Exp ::= Exp "/" Exp [kSymbol(d)] syntax priority true > p > d""" , """syntax Exp ::= "true" > Exp "+" Exp [kSymbol(p)] > Exp "/" Exp [kSymbol(d)]""")
             )

    prioritiesTests foreach { strings => assertEquals(parsePrettySentences(strings._1), parsePrettySentences(strings._2)) }
  }

  @Test def ruleParsingTest(): Unit = {
    import ExpDefinition._

    val ruleTests: Seq[(Sentence, String)]
        = Seq( (rule(term("p", term("3"), term("3")), term("6"))                                    , """rule p(3,3) => 6"""     )
             , (rule(term("m", term("t", term("4"), term("3")), term("9")), term("3"))              , """rule m(t(4,3),9) => 3""")
             , (rule(term("p", term("2"), term("2")), term("4"))                                    , """rule 2 + 2 => 4"""      )
             , (rule(term("p", Variable("E1", "Exp"), Variable("E2", "Exp")), term("0"))            , """rule E1:Exp + E2:Exp => 0""")
             , (rule(term("p", Variable("E1", "Exp"), Variable("E2", "Exp")), Variable("E1", "Exp")), """rule E1:Exp + E2:Exp => E1:Exp""")
             //, (rule(term("p", term("2"), term("t", term("3"), term("2"))), term("8")) , """rule 2 + 3 * 2 => 8"""  )
             )

    val ruleParser = mkParser(mkRuleParserDefinition(ekoreToKore(preProcess(parseK(expString, "KDefinition")))))

    ruleTests foreach { strings => assertEquals(strings._1, downSentence(resolveRule(ruleParser)(preProcess(parseK(strings._2, "KSentence"))))) }
  }

  @Test def lambdaTest(): Unit = {
    val LAMBDA_STRING = io.Source.fromFile("src/test/scala/org/kframework/parser/lambda.k").mkString
    val lambda_parsed = ekoreToKore(preProcess(parseK(LAMBDA_STRING, "KDefinition")))
    println(lambda_parsed)
    val lambda_downed = downDefinition(resolveDefinitionRules(lambda_parsed))
    println(lambda_downed)
  }

}
