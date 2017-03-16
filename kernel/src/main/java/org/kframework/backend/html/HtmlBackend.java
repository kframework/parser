// Copyright (c) 2012-2016 K Team. All Rights Reserved.
package org.kframework.backend.html;

import org.apache.commons.io.FilenameUtils;
import org.kframework.backend.PosterBackend;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.file.FileUtil;

public class HtmlBackend extends PosterBackend {

    private final Context context;
    private final FileUtil files;

    public HtmlBackend(Stopwatch sw, Context context, FileUtil files) {
        super(sw);
        this.context = context;
        this.files = files;
    }

    @Override
    public void run() {
        HTMLFilter htmlFilter = new HTMLFilter(context);
//        htmlFilter.visitNode(definition);

        String html = htmlFilter.getHTML();

//        files.saveToDefinitionDirectory(FilenameUtils.removeExtension(definition.getMainFile().getName()) + ".html", html);
        files.saveToDefinitionDirectory("k-definition.css", files.loadFromKBase("include/html/k-definition.css"));

        sw.printIntermediate("Generating HTML");

    }
}
