// Turn this project into a Scala.js project by importing these settings
enablePlugins(ScalaJSPlugin)

name := "fragger"

organization := "uk.ac.ed.inf"

version := "0.1"

scalaVersion := "2.11.6"

persistLauncher in Compile := true

persistLauncher in Test := false

// relativeSourceMaps := true

resolvers += "Sonatype snapshots" at
  "https://oss.sonatype.org/content/repositories/snapshots/"

libraryDependencies ++= Seq(
  "org.scala-js" %%% "scalajs-dom" % "0.8.0",
  "com.lihaoyi" %%% "scalatags" % "0.5.2",
  "org.scala-js" %%% "scala-parser-combinators" % "1.0.2",
  "uk.ac.ed.inf" %%% "graph-rewriting" % "0.2"
)
