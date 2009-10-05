#!/usr/bin/ruby
Dir["src/**/*.agda"].each {|filename|
  dependencies = File.readlines(filename).grep(/^open import /).map {|line|
    line.chomp.split(/[( )]/)[2].gsub(".", "/")
  } + File.readlines(filename).grep(/^import /).map {|line|
    line.chomp.split(/[( )]/)[1].gsub(".", "/")
  }
  agda_dependencies = dependencies.select {|d|
    File.exists?("src/#{d}.agda")
  }.map {|d|
    "crumbs/#{d}.agda"
  }
  m4_dependencies = dependencies.select {|d|
    File.exists?("src/#{d}.m4")
  }.map {|d|
    "src/#{d}.m4"
  }
  
  agda_file = "crumbs/#{filename.gsub(/^src\//, "")}"
  dependencies = [filename] + agda_dependencies + m4_dependencies
  m4_files = m4_dependencies.join(" ")
  m4_len = 1
  m4_dependencies.each {|f|
    m4_len += File.readlines(f).length
  }
  puts "#{agda_file}: #{dependencies.join(" ")}"
  puts "\tmkdir -p #{File.dirname(agda_file)}"
  puts "\tm4 #{m4_files} $< | tail -n +#{m4_len} > $@"
}
